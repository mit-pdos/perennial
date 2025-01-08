package operations

type Operation struct {
	OperationType uint64
	VersionVector []uint64
	Data          uint64
}

func equalSlices(s1 []uint64, s2 []uint64) bool {
	var output = true
	var i = uint64(0)
	var l = uint64(len(s1))

	for i < l {
		if s1[i] != s2[i] {
			output = false
			break
		}
		i++
	}

	return output
}

func equalOperations(o1 *Operation, o2 *Operation) bool {
	return (o1.OperationType == o2.OperationType) && equalSlices(o1.VersionVector, o2.VersionVector) && (o1.Data == o2.Data)
}


func deleteAtIndex(l []Operation, index uint64) []Operation {
        var ret = make([]Operation, 0)
	ret = append(ret, l[:index]...)
	return append(ret, l[index+1:]...)
}