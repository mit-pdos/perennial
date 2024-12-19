package sort

func BinarySearch(s []uint64, needle uint64) (uint64, bool) {
	var i = uint64(0)
	var j = uint64(len(s))
	for i < j {
		mid := i + (j-i)/2
		if s[mid] < needle {
			i = mid + 1
		} else {
			j = mid
		}
	}
	if i < uint64(len(s)) {
		return i, s[i] == needle
	}
	return i, false
}

func insert(s []uint64, value uint64) []uint64 {
	index, duplicate := BinarySearch(s, value)
	if duplicate {
		return s
	}
	return append(s[:index+1], s[index:]...)
}
