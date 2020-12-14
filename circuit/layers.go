package circuit

import (
	"gkr-mimc/common"
	"gkr-mimc/polynomial"

	"github.com/consensys/gurvy/bn256/fr"
)

// Wire represent a single connexion between a gate,
// its output and its inputs
type Wire struct {
	L, R, O int
	Gate    Gate
}

// Layer describes how a layer feeds its inputs
type Layer struct {
	Wires               []Wire
	BGInputs, BGOutputs int
	Gates               []Gate
}

// NewLayer construct a new layer from a list of wires
func NewLayer(wires []Wire) Layer {
	return Layer{
		Wires:     wires,
		Gates:     Gates(wires),
		BGInputs:  BGInputs(wires),
		BGOutputs: BGOutputs(wires),
	}
}

// GetStaticTable returns the prefolded static tables
// They are returned in the same order as l.Gates
func (l *Layer) GetStaticTable(q []fr.Element) []polynomial.BookKeepingTable {
	// Computes the gates to ensure we return the bookeeping tables in a deterministic order
	gates := l.Gates
	res := make([]polynomial.BookKeepingTable, len(gates))
	// Usefull integer constants
	gO, gL := (1 << (2 * l.BGInputs)), 1<<l.BGInputs
	var one fr.Element
	one.SetOne()

	for i, gate := range l.Gates {
		// The tab is filled with zeroes
		tab := make([]fr.Element, (1<<l.BGOutputs)*(1<<(2*l.BGInputs)))
		for _, w := range l.Wires {
			if w.Gate.ID() == gate.ID() {
				k := gO*w.O + gL*w.L + w.R
				tab[k].Add(&tab[k], &one)
			}
		}
		// Prefold the bookkeeping table before returning
		bkt := polynomial.NewBookKeepingTable(tab)
		for _, r := range q {
			bkt.Fold(r)
		}
		res[i] = bkt
	}

	return res
}

// Evaluate returns the assignment of the next layer
// It can be multi-threaded
func (l *Layer) Evaluate(inputs [][]fr.Element, nCore int) [][]fr.Element {
	res := make([][]fr.Element, len(inputs))

	GInputs := 1 << l.BGInputs
	GOutputs := 1 << l.BGOutputs

	common.Execute(len(inputs), func(start, end int) {

		var subRes []fr.Element

		for i := start; i < end; i++ {
			inps := inputs[i]
			N := len(inps) / GInputs
			if len(subRes) < N*GOutputs {
				subRes = make([]fr.Element, N*GOutputs)
			} else {
				subRes = subRes[:N*GOutputs]
				for j := 0; j < len(subRes); j++ {
					subRes[j].SetZero()
				}
			}
			var tmp fr.Element
			for _, w := range l.Wires {
				// Precompute the indices
				wON := w.O * N
				wLN := w.L * N
				wRN := w.R * N
				for h := 0; h < N; h++ {
					// Runs the gate evaluator
					w.Gate.Eval(&tmp, &inps[wLN+h], &inps[wRN*N+h])
					subRes[wON+h].Add(&subRes[wON+h], &tmp)
				}
			}
			res[i] = subRes
		}
	})
	return res
}

// BGOutputs return the log-size of the input layer of the layer
func BGOutputs(wires []Wire) int {
	res := 0
	for _, wire := range wires {
		if res < wire.O {
			res = wire.O
		}
	}
	return common.Log2Ceil(res + 1)
}

// BGInputs return the log-size of the input layer of the layer
func BGInputs(wires []Wire) int {
	res := 0
	for _, wire := range wires {
		if res < wire.L {
			res = wire.L
		}
		if res < wire.R {
			res = wire.R
		}
	}
	return common.Log2Ceil(res + 1)
}

// Gates returns a deduplicated list of gates used by this layer
func Gates(wires []Wire) []Gate {
	gates := make(map[string]Gate)
	res := []Gate{}
	for _, wire := range wires {
		if _, ok := gates[wire.Gate.ID()]; !ok {
			res = append(res, wire.Gate)
		}
	}
	return res
}
