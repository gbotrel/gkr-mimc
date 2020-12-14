package sumcheck

import (
	"gkr-mimc/circuit"
	"gkr-mimc/common"
	"gkr-mimc/polynomial"

	"github.com/consensys/gurvy/bn256/fr"
)

// MultiThreadedProver can process on several threads
type MultiThreadedProver struct {
	// Contains the values of the previous layer
	vL []polynomial.BookKeepingTable
	vR []polynomial.BookKeepingTable
	// Contains the static tables defining the circuit structure
	eq           []polynomial.BookKeepingTable
	gates        []circuit.Gate
	staticTables []polynomial.BookKeepingTable
	// Degrees for the differents variables
	degreeHL     int
	degreeHR     int
	degreeHPrime int
}

type indexedProver struct {
	I int
	P SingleThreadedProver
}

// NewMultiThreadedProver constructs a new prover
func NewMultiThreadedProver(
	vL []polynomial.BookKeepingTable,
	vR []polynomial.BookKeepingTable,
	eq []polynomial.BookKeepingTable,
	gates []circuit.Gate,
	staticTables []polynomial.BookKeepingTable,
) MultiThreadedProver {
	// Auto-computes the degree on each variables
	degreeHL, degreeHR, degreeHPrime := 0, 0, 0
	for _, gate := range gates {
		dL, dR, dPrime := gate.Degrees()
		degreeHL = common.Max(degreeHL, dL)
		degreeHR = common.Max(degreeHR, dR)
		degreeHPrime = common.Max(degreeHPrime, dPrime)
	}
	return MultiThreadedProver{
		vL:           vL,
		vR:           vR,
		eq:           eq,
		gates:        gates,
		staticTables: staticTables,
		degreeHL:     degreeHL + 1,
		degreeHR:     degreeHR + 1,
		degreeHPrime: degreeHPrime + 1,
	}
}

// GetClaim returns the sum of all evaluations don't call after folding
func (p *MultiThreadedProver) GetClaim(nCore int) fr.Element {
	// Define usefull constants
	nChunks := len(p.eq)
	evalsChan := make(chan fr.Element, len(p.eq))
	semaphore := common.NewSemaphore(nCore)

	for i := 0; i < nChunks; i++ {
		go p.GetClaimForChunk(i, evalsChan, semaphore)
	}

	var res fr.Element
	for i := 0; i < nChunks; i++ {
		x := <-evalsChan
		res.Add(&x, &res)
	}

	return res
}

// Prove runs a prover with multi-threading
func (p *MultiThreadedProver) Prove(nCore int) (proof Proof, qPrime, qL, qR, finalClaims []fr.Element) {

	// Define usefull constants
	nChunks := len(p.eq)
	n := nChunks * len(p.eq[0].Table)     // Number of subcircuit. Since we haven't fold on h' yet
	g := nChunks * len(p.vL[0].Table) / n // SubCircuit size. Since we haven't fold on hR yet
	bN := common.Log2Ceil(n)
	bG := common.Log2Ceil(g)
	logNChunk := common.Log2Ceil(nChunks)

	// Initialized the results
	proof.PolyCoeffs = make([][]fr.Element, bN+2*bG)
	qPrime = make([]fr.Element, bN)
	qL = make([]fr.Element, bG)
	qR = make([]fr.Element, bG)
	finalClaims = make([]fr.Element, 3+len(p.staticTables))

	// Initialize the channels
	evalsChan := make(chan []fr.Element, nChunks)
	finChan := make(chan int, nChunks)
	rChans := make([]chan fr.Element, nChunks)

	subProvers := make([]*SingleThreadedProver, nChunks)

	var evaledStaticTables [][][]fr.Element
	var staticIsNotZero [][]bool

	// create the sub-provers
	for i := 0; i < nChunks; i++ {
		subProvers[i] = NewSingleThreadedProver(
			p.vL[i],
			p.vR[i],
			p.eq[i],
			p.gates,
			p.staticTables,
		)
	}

	updatedPrecomputedStaticTables := func(hr bool) {
		// Define usefull constants
		n := len(subProvers[0].eq.Table)                      // Number of subcircuit. Since we haven't fold on h' yet
		g := len(subProvers[0].vR.Table) / n                  // SubCircuit size. Since we haven't fold on hR yet
		lenHL := len(subProvers[0].staticTables[0].Table) / g // Number of remaining variables on R
		nGate := len(subProvers[0].staticTables)              // Number of different gates
		nEvals := subProvers[0].degreeHL + 1
		if hr {
			nEvals = subProvers[0].degreeHR + 1
		}

		// PreEvaluates the bookKeepingTable so we can reuse them results multiple time later
		if len(evaledStaticTables) < nGate {
			evaledStaticTables = make([][][]fr.Element, nGate)
		} else {
			evaledStaticTables = evaledStaticTables[:nGate]
		}

		// staticIsNotZero tracks the values of hL and hR at which the staticTable cancels
		// so that we can avoid computing gates evaluation and multiplying the result by zero after
		if len(staticIsNotZero) < nGate {
			staticIsNotZero = make([][]bool, nGate)
		} else {
			staticIsNotZero = staticIsNotZero[:nGate]
		}
		for i, tab := range p.staticTables {
			preEvaluatedStaticTables := tab.FunctionEvals()
			lenI := lenHL * g / 2
			if len(staticIsNotZero[i]) < lenI {
				staticIsNotZero[i] = make([]bool, lenI)
				evaledStaticTables[i] = make([][]fr.Element, lenI)
			} else {
				staticIsNotZero[i] = staticIsNotZero[i][:lenI]
				evaledStaticTables[i] = evaledStaticTables[i][:lenI]
			}

			for h := range staticIsNotZero[i] {
				staticIsNotZero[i][h] = !(tab.Table[h].IsZero() &&
					preEvaluatedStaticTables[h].IsZero())
				// Computes all the preEvaluations of the staticTables
				if len(evaledStaticTables[i][h]) < nEvals {
					evaledStaticTables[i][h] = make([]fr.Element, nEvals)
				} else {
					evaledStaticTables[i][h] = evaledStaticTables[i][h][:nEvals]
				}
				evaledStaticTables[i][h][0] = tab.Table[h]
				for t := 1; t < nEvals; t++ {
					evaledStaticTables[i][h][t].Add(
						&evaledStaticTables[i][h][t-1],
						&preEvaluatedStaticTables[h],
					)
				}
			}
		}
	}
	updatedPrecomputedStaticTables(false)

	// run the subprovers
	for i := 0; i < nChunks; i++ {
		rChans[i] = make(chan fr.Element, 1)
		subProvers[i].evaledStaticTables = evaledStaticTables
		subProvers[i].staticIsNotZero = staticIsNotZero
		go subProvers[i].Run(i, evalsChan, rChans[i], finChan)
	}

	// Process on all values until all the subprover are completely fold
	for i := 0; i < 2*bG+bN-logNChunk; i++ {
		evals := ConsumeAccumulate(evalsChan, nChunks)
		proof.PolyCoeffs[i] = polynomial.InterpolateOnRange(evals)
		r := common.GetChallenge(proof.PolyCoeffs[i])
		if i < 2*bG {
			// on HL and HR only
			// TODO @gbotrel might not be very helpful to paralellize, need to try with bigger circuits
			// common.Execute(len(p.staticTables), func(start, end int) {
			// 	for j := start; j < end; j++ {
			// 		p.staticTables[j].Fold(r)
			// 	}
			// })
			for j := 0; j < len(p.staticTables); j++ {
				p.staticTables[j].Fold(r)
			}

			// we also update evaledStaticTables, staticIsNotZero
			updatedPrecomputedStaticTables(i >= bG-1)
			for j := 0; j < nChunks; j++ {
				subProvers[j].evaledStaticTables = evaledStaticTables
				subProvers[j].staticIsNotZero = staticIsNotZero
			}

		}

		Broadcast(rChans, r)
		if i < bG {
			qL[i] = r
		} else if i < 2*bG {
			qR[i-bG] = r
		} else {
			qPrime[i-2*bG] = r
		}
	}

	newP := ConsumeMergeProvers(finChan, subProvers, nChunks)

	// Finishes on hPrime. Identical to the single-threaded implementation
	for i := 2*bG + bN - logNChunk; i < bN+2*bG; i++ {
		evals := newP.GetEvalsOnHPrime()
		proof.PolyCoeffs[i] = polynomial.InterpolateOnRange(evals)
		r := common.GetChallenge(proof.PolyCoeffs[i])
		newP.FoldHPrime(r)
		qPrime[i-2*bG] = r
	}

	finalClaims[0] = newP.vL.Table[0]
	finalClaims[1] = newP.vR.Table[0]
	finalClaims[2] = newP.eq.Table[0]
	for i, bkt := range newP.staticTables {
		finalClaims[3+i] = bkt.Table[0]
	}

	close(evalsChan)
	close(finChan)

	return proof, qPrime, qL, qR, finalClaims

}

// ConsumeMergeProvers reallocate the provers from the content of the indexed prover,
// by concatenating their bookkeeping tables.
func ConsumeMergeProvers(ch chan int, subProvers []*SingleThreadedProver, nToMerge int) *SingleThreadedProver {

	// Allocate the new Table
	newVL := make([]fr.Element, nToMerge)
	newVR := make([]fr.Element, nToMerge)
	newEq := make([]fr.Element, nToMerge)

	indexed := <-ch
	// First off the loop to take the static tables at the same time
	newVL[indexed] = subProvers[indexed].vL.Table[0]
	newVR[indexed] = subProvers[indexed].vR.Table[0]
	newEq[indexed] = subProvers[indexed].eq.Table[0]
	// All subProvers have the same staticTables. So we can take the first one
	staticTables := subProvers[indexed].staticTables
	gates := subProvers[indexed].gates

	for i := 0; i < nToMerge-1; i++ {
		indexed = <-ch
		newVL[indexed] = subProvers[indexed].vL.Table[0]
		newVR[indexed] = subProvers[indexed].vR.Table[0]
		newEq[indexed] = subProvers[indexed].eq.Table[0]
	}

	return NewSingleThreadedProver(
		polynomial.NewBookKeepingTable(newVL),
		polynomial.NewBookKeepingTable(newVR),
		polynomial.NewBookKeepingTable(newEq),
		gates,
		staticTables,
	)
}

// ConsumeAccumulate consumes `nToConsume` elements from `ch`,
// and return their sum Element-wise
func ConsumeAccumulate(ch chan []fr.Element, nToConsume int) []fr.Element {
	res := <-ch
	for i := 0; i < nToConsume-1; i++ {
		tmp := <-ch
		for i := range res {
			res[i].Add(&res[i], &tmp[i])
		}
	}
	return res
}

// Broadcast broadcasts r, to all channels
func Broadcast(chs []chan fr.Element, r fr.Element) {
	for _, ch := range chs {
		ch <- r
	}
}

// GetClaimForChunk runs GetClaim on a chunk, and is aimed at being run in the Background
func (p *MultiThreadedProver) GetClaimForChunk(chunkIndex int, evalsChan chan fr.Element, semaphore common.Semaphore) {
	semaphore.Acquire()
	defer semaphore.Release()

	// Deep-copies the static tables
	staticTablesCopy := make([]polynomial.BookKeepingTable, len(p.staticTables))
	for i := range staticTablesCopy {
		staticTablesCopy[i] = p.staticTables[i].DeepCopy()
	}

	subProver := NewSingleThreadedProver(
		p.vL[chunkIndex],
		p.vR[chunkIndex],
		p.eq[chunkIndex],
		p.gates,
		staticTablesCopy,
	)

	evalsChan <- subProver.GetClaim()
}

// Run runs thread with a partial prover
func (subProver *SingleThreadedProver) Run(
	chunkIndex int,
	evalsChan chan []fr.Element,
	rChan chan fr.Element,
	finChan chan int,
) {

	// Define usefull constants
	n := len(subProver.eq.Table)     // Number of subcircuit. Since we haven't fold on h' yet
	g := len(subProver.vR.Table) / n // SubCircuit size. Since we haven't fold on hR yet
	bN := common.Log2Ceil(n)
	bG := common.Log2Ceil(g)

	// Run on hL
	for i := 0; i < bG; i++ {
		evalsChan <- subProver.accumulateEvalsOnHL(subProver.evaledStaticTables, subProver.staticIsNotZero)
		subProver.vL.Fold(<-rChan)
	}

	// Run on hR
	for i := 0; i < bG; i++ {
		evalsChan <- subProver.accumulateEvalsOnHR(subProver.staticIsNotZero, subProver.evaledStaticTables)
		subProver.vR.Fold(<-rChan)
	}

	// Run on hPrime
	for i := 0; i < bN; i++ {
		evalsChan <- subProver.GetEvalsOnHPrime()
		subProver.FoldHPrime(<-rChan)
	}

	finChan <- chunkIndex
	close(rChan)
}
