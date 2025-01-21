package processClientRequest

type Operation struct {
	OperationType uint64
	VersionVector []uint64
	Data          uint64
}

type Request struct {
	RequestType uint64

	Client_OperationType uint64
	Client_SessionType   uint64
	Client_Data          uint64
	Client_Vector        []uint64


	Receive_Gossip_ServerId   uint64
	Receive_Gossip_Operations []Operation

	Acknowledge_Gossip_ServerId uint64
	Acknowledge_Gossip_Index    uint64

	Receiver_ServerId uint64
}

type Reply struct {
	ReplyType uint64

	Client_Succeeded     bool
	Client_OperationType uint64
	Client_Data          uint64
	Client_Vector        []uint64
}

type Server struct {
	Id                     uint64
	NumberOfServers        uint64
	VectorClock            []uint64
	OperationsPerformed    []Operation
	MyOperations           []Operation
	PendingOperations      []Operation
	Data                   uint64
	GossipAcknowledgements []uint64
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

func maxTwoInts(x uint64, y uint64) uint64 {
	if x > y {
		return x
	} else {
		return y
	}
}

func maxTS(t1 []uint64, t2 []uint64) []uint64 {
	var i = uint64(0)
	var length = uint64(len(t1))
	var output = make([]uint64, len(t1))
	for i < length {
		output[i] = maxTwoInts(t1[i], t2[i])
		i += 1
	}
	return output
}

func dependencyCheck(TS []uint64, request Request) bool {
	return compareVersionVector(TS, request.Client_Vector)
}

func processClientRequest(server Server, request Request) (Server, Reply) {
	reply := Reply{}

	if !(dependencyCheck(server.VectorClock, request)) {
		reply.Client_Succeeded = false
		return server, reply
	}

	if request.Client_OperationType == 0 {
		reply.Client_Succeeded = true
		reply.Client_OperationType = 0
		reply.Client_Data = server.Data
		reply.Client_Vector = maxTS(request.Client_Vector, server.VectorClock)

		return server, reply
	} else {
		server.VectorClock[server.Id] += 1
		server.Data = request.Client_Data

		op := Operation{
			OperationType: 1,
			VersionVector: append([]uint64(nil), server.VectorClock...),
			Data:          server.Data,
		}

		server.OperationsPerformed = append(server.OperationsPerformed, op) // would we need to do anything here since we are mutating the underlying slice?
		server.MyOperations = append(server.MyOperations, op)               // we can reuse op because it should be immutable

		reply.Client_Succeeded = true
		reply.Client_OperationType = 1
		reply.Client_Data = server.Data
		reply.Client_Vector = append([]uint64(nil), server.VectorClock...)
		return server, reply
	}
}

func acknowledgeGossip(server Server, request Request) Server {
	server.GossipAcknowledgements[request.Acknowledge_Gossip_ServerId] = request.Acknowledge_Gossip_Index
	return server
}


func getGossipOperations(server Server, serverId uint64) []Operation {
     	output := make([]Operation, 0)
	return append(output, server.MyOperations[server.GossipAcknowledgements[serverId]:]...)
}
