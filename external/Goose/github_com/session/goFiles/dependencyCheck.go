package dependencyCheck

type Server struct {
	Id    uint64
	Data  uint64
	VectorClock []uint64
}

type ClientRequest struct {
	OperationType uint64
	Data          uint64
	ReadVector    []uint64
	WriteVector   []uint64
}

type ClientReply struct {
	Succeeded     bool
	OperationType uint64
	Data          uint64
}

func compareVersionVector(v1 []uint64, v2 []uint64) bool {
	var output = true
	var i = uint64(0)
	var l = uint64(len(v1))
	for i < l {
		if v1[i] < v2[i] {
			output = false
			break
		}
		i++
	}
	return output
}

func concurrentVersionVector(v1 []uint64, v2 []uint64) bool {
     return !compareVersionVector(v1, v2) && !compareVersionVector(v2, v1)
}

func lexiographicCompare(v1 []uint64, v2 []uint64) bool {
        var output = true
     	var i = uint64(0)
      	var l = uint64(len(v1))
	for i < l {
	        if v1[i] == v2[i] {
		   i++ 
		} else {
		     output = v1[i] > v2[i]
		     break 
		}
	}
	
	return output 
}

func compareVersionVectorTotal(v1 []uint64, v2 []uint64) bool {
     if concurrentVersionVector(v1, v2) {
     	return lexiographicCompare(v1, v2)
     }
     
     return compareVersionVector(v1, v2)
}

func dependencyCheck(server Server, request ClientRequest) bool {
	if (request.OperationType == 0) { // Monotonic Reads
		return compareVersionVector(server.VectorClock, request.ReadVector)
	}
	if (request.OperationType == 1) { // Writes Follow Reads
		return compareVersionVector(server.VectorClock, request.ReadVector)
	}
	if (request.OperationType == 2) { // Read Your Writes 
		return compareVersionVector(server.VectorClock, request.WriteVector)
	}
	if (request.OperationType == 3) { // Monotonics Writes
		return compareVersionVector(server.VectorClock, request.WriteVector)
	}
	if (request.OperationType == 4) { // Causal
		return (compareVersionVector(server.VectorClock, request.ReadVector) && compareVersionVector(server.VectorClock, request.WriteVector))
	}
	
	panic("Invalid Operation Number")
}
