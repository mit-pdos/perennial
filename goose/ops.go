package goose

import (
	"go/token"

	"github.com/mit-pdos/perennial/goose/glang"
)

var gooseLangOps = map[token.Token]glang.OpId{
	token.EQL: glang.OpEquals,
	token.NEQ: glang.OpNotEquals,
	token.ADD: glang.OpPlus,
	token.LSS: glang.OpLessThan,
	token.GTR: glang.OpGreaterThan,
	token.SUB: glang.OpMinus,
	token.MUL: glang.OpMul,
	token.QUO: glang.OpQuot,
	token.REM: glang.OpRem,
	token.LEQ: glang.OpLessEq,
	token.GEQ: glang.OpGreaterEq,
	token.SHL: glang.OpShl,
	token.SHR: glang.OpShr,

	token.LAND:    glang.OpLAnd,
	token.LOR:     glang.OpLOr,
	token.AND:     glang.OpAnd,
	token.AND_NOT: glang.OpAndNot,
	token.OR:      glang.OpOr,
	token.XOR:     glang.OpXor,

	token.NOT: glang.OpNot,
}
