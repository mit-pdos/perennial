# Recover (`recovers/`), plan A (`F'deferred` taking `$recover`)
- methodRecover, topRecover, recoverNotPanicking, printArg (handleMethods/catchPanic): `defer c.catch(&x)` → `defer (catcher.catch'deferred $panic c &x)`. Provable.
- repanic, nestedPanic: `F'deferred` re-panics after `recoverPanic $recover`. Provable.
- methodValueRecover (`f := c.catch; defer f(&x)`): goose cannot see the callee, so it runs the ordinary `catch`, whose `recover()` is stuck. Unprovable, and sound. Returning nil there would let the false "panics with 9" spec be proved.
- directCall, helperInDeferredLiteral: Go's recover gives nil. Under "stuck" they are unprovable. That is the incompleteness decision point 6 accepts, and these two show its price.
