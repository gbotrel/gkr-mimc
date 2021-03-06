package gkr

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gurvy/bn256/fr"
)

// Gate evaluate either a cipherGate or a copy gate
type Gate func(cs *frontend.ConstraintSystem, vL, vR frontend.Variable) frontend.Variable

// CipherGate returns a cipher gate
func CipherGate(ark fr.Element) Gate {
	return func(cs *frontend.ConstraintSystem, vL, vR frontend.Variable) frontend.Variable {
		tmp := cs.Add(vR, cs.Constant(ark))
		cipher := cs.Mul(tmp, tmp)
		cipher = cs.Mul(cipher, tmp)
		cipher = cs.Mul(cipher, cipher)
		cipher = cs.Mul(cipher, tmp)
		return cs.Add(cipher, vL)
	}
}

// CopyGate returns a copy gate
func CopyGate() Gate {
	return func(cs *frontend.ConstraintSystem, vL, vR frontend.Variable) frontend.Variable {
		return vL
	}
}
