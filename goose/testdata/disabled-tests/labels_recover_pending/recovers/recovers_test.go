package recovers

import "testing"

// Each test* function of package recovers returns true in Go.
func TestMethodRecover(t *testing.T) {
	if !testMethodRecover() {
		t.Fatal("testMethodRecover returned false")
	}
}

func TestTopRecover(t *testing.T) {
	if !testTopRecover() {
		t.Fatal("testTopRecover returned false")
	}
}

func TestRepanic(t *testing.T) {
	if !testRepanic() {
		t.Fatal("testRepanic returned false")
	}
}

func TestRecoverNotPanicking(t *testing.T) {
	if !testRecoverNotPanicking() {
		t.Fatal("testRecoverNotPanicking returned false")
	}
}

func TestMethodValueRecover(t *testing.T) {
	if !testMethodValueRecover() {
		t.Fatal("testMethodValueRecover returned false")
	}
}

func TestDirectCall(t *testing.T) {
	if !testDirectCall() {
		t.Fatal("testDirectCall returned false")
	}
}

func TestHelperInDeferredLiteral(t *testing.T) {
	if !testHelperInDeferredLiteral() {
		t.Fatal("testHelperInDeferredLiteral returned false")
	}
}

func TestHandleMethodsGood(t *testing.T) {
	if !testHandleMethodsGood() {
		t.Fatal("testHandleMethodsGood returned false")
	}
}

func TestHandleMethodsBad(t *testing.T) {
	if !testHandleMethodsBad() {
		t.Fatal("testHandleMethodsBad returned false")
	}
}

func TestHandleMethodsNotStringer(t *testing.T) {
	if !testHandleMethodsNotStringer() {
		t.Fatal("testHandleMethodsNotStringer returned false")
	}
}

func TestNestedPanic(t *testing.T) {
	if !testNestedPanic() {
		t.Fatal("testNestedPanic returned false")
	}
}
