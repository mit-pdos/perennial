package canApply

func oneOffVersionVector(serverId uint64, v1 []uint64, v2 []uint64) bool {
        var output = true
	var canApply = true
	var i = uint64(0)
	var l = uint64(len(v1))

	for i < l {
		if i == uint64(serverId) {
		     	i++ 
			continue
		} else if (canApply && v1[i]+1 == v2[i]) {
			canApply = false
			i++
			continue
		} else if v1[i] < v2[i] {
		        output = false
			i++ 
		}
	}
	
	return output
}