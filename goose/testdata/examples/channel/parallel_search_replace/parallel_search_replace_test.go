package parallel_search_replace

import (
	"testing"
)

func TestSearchReplace(t *testing.T) {
	tests := []struct {
		name     string
		input    []int
		x        int
		y        int
		expected []int
	}{
		{
			name:     "empty slice",
			input:    []int{},
			x:        1,
			y:        2,
			expected: []int{},
		},
		{
			name:     "single element match",
			input:    []int{5},
			x:        5,
			y:        10,
			expected: []int{10},
		},
		{
			name:     "single element no match",
			input:    []int{5},
			x:        3,
			y:        10,
			expected: []int{5},
		},
		{
			name:     "small slice with matches",
			input:    []int{1, 2, 3, 1, 4, 1},
			x:        1,
			y:        99,
			expected: []int{99, 2, 3, 99, 4, 99},
		},
		{
			name:     "small slice no matches",
			input:    []int{1, 2, 3, 4, 5},
			x:        99,
			y:        100,
			expected: []int{1, 2, 3, 4, 5},
		},
		{
			name:     "all elements match",
			input:    []int{7, 7, 7, 7, 7},
			x:        7,
			y:        14,
			expected: []int{14, 14, 14, 14, 14},
		},
		{
			name:     "large slice with multiple workers",
			input:    make([]int, 10000),
			x:        0,
			y:        42,
			expected: make([]int, 10000),
		},
	}

	// Initialize the large test case
	for i := range tests[len(tests)-1].input {
		tests[len(tests)-1].input[i] = 0
	}
	for i := range tests[len(tests)-1].expected {
		tests[len(tests)-1].expected[i] = 42
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			SearchReplace(tt.input, tt.x, tt.y)

			// Verify the result
			if len(tt.input) != len(tt.expected) {
				t.Errorf("length mismatch: got %d, want %d", len(tt.input), len(tt.expected))
				return
			}

			for i := range tt.input {
				if tt.input[i] != tt.expected[i] {
					t.Errorf("at index %d: got %d, want %d", i, tt.input[i], tt.expected[i])
				}
			}
		})
	}
}

func TestSearchReplacePatternedData(t *testing.T) {
	// Test with a large slice that has a specific pattern
	size := 15000
	input := make([]int, size)

	// Every 10th element is -1, rest are sequential
	for i := 0; i < size; i++ {
		if i%10 == 0 {
			input[i] = -1
		} else {
			input[i] = i
		}
	}

	SearchReplace(input, -1, 100)

	// Verify all -1s were replaced with 100
	for i := 0; i < size; i++ {
		if i%10 == 0 {
			if input[i] != 100 {
				t.Errorf("at index %d: expected 100, got %d", i, input[i])
			}
		} else {
			if input[i] != i {
				t.Errorf("at index %d: expected %d, got %d", i, i, input[i])
			}
		}
	}
}

func TestSearchReplaceNegativeNumbers(t *testing.T) {
	input := []int{-5, 10, -5, 20, -5, 30}
	SearchReplace(input, -5, -99)

	expected := []int{-99, 10, -99, 20, -99, 30}
	for i := range input {
		if input[i] != expected[i] {
			t.Errorf("at index %d: got %d, want %d", i, input[i], expected[i])
		}
	}
}

func TestSearchReplaceZeroValue(t *testing.T) {
	input := []int{0, 1, 0, 2, 0, 3}
	SearchReplace(input, 0, 42)

	expected := []int{42, 1, 42, 2, 42, 3}
	for i := range input {
		if input[i] != expected[i] {
			t.Errorf("at index %d: got %d, want %d", i, input[i], expected[i])
		}
	}
}
