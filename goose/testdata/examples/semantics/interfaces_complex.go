package semantics

// ----------------------------
// Failing:
// - Slices
// - Maps
// - Empty interface
// - String interface
// ----------------------------

func testParamsInterface() bool {
	s := SquareStruct{
		Side: 3,
	}
	volume := measureVolumePlusNM(s, 1, 2)
	return volume == 30
}

func testEmptyInterface() bool {
	var i interface{}
	var j interface{}
	return i == j
}

func testStringInterface() bool {
	var i interface{} = "string"
	var j interface{} = "string"
	return i == j
}

type NumStruct struct {
	Value int
}

func testTypeAssertionInterface() bool {
	var i interface{} = NumStruct{3}
	return i.(NumStruct) == NumStruct{3}
}

type shapeInterface interface {
	describe() string
}

type polygonInterface interface {
	sides() uint64
}

type shapeStruct struct {
	Shape string
}

func (s shapeStruct) describe() string {
	return s.Shape
}

type polygonStruct struct {
	Shape string
	Sides uint64
}

func (p polygonStruct) describe() string {
	return p.Shape
}

func (p polygonStruct) sides() uint64 {
	return p.Sides
}

func testDoublePointerInterface() bool {
	s := shapeStruct{"circle"}
	shapes := []shapeInterface{s, &s}
	s.Shape = "square"
	return shapes[0].describe() != shapes[1].describe()
}

func testMultipleFieldsInterface() bool {
	s := polygonStruct{"triangle", 3}
	return s.Shape == "triangle" && s.Sides == 3
}

type dogInterface interface {
	Name() string
	Speed() uint64
}

type catInterface interface {
	Name() string
	Weight() uint64
}

type Puppy string

func (p Puppy) Name() string {
	return "Max"
}

func (p Puppy) Speed() uint64 {
	return 1
}

type Kitten string

func (k Kitten) Name() string {
	return "Max"
}

func (k Kitten) Weight() uint64 {
	return 10
}

func testSharedFunctionsInterface() bool {
	var kit catInterface = Kitten("Kitten")
	var pup dogInterface = Puppy("Puppy")
	return pup.Name() == kit.Name()
}

type printInterface interface {
	Assign(string)
	GetTitle() string
}

type PaperStruct struct {
	Title string
}

func (p *PaperStruct) Assign(t string) {
	p.Title = t
}

func (p *PaperStruct) GetTitle() string {
	return p.Title
}

func testAcceptAddressInterface() bool {
	var p1 PaperStruct
	var p2 PaperStruct
	p1.Assign("Sample Title")
	p2.Assign("Sample Title")
	var print1 printInterface
	var print2 printInterface
	print1 = &p1
	print2 = &p2
	return print1.GetTitle() == print2.GetTitle()
}

type Flower interface {
	Petals() uint64
}

type Flora interface {
	Flower
	Genus() string
}

type Lily struct{}

func (l Lily) Petals() uint64 { return 3 }
func (l Lily) Genus() string  { return "Lillium" }

type Rose struct{}

func (r Rose) Petals() uint64 { return 12 }
func (r Rose) Genus() string  { return "Rosa" }

type Daisy struct{}

func (d Daisy) Petals() uint64 { return 5 }
func (d Daisy) Genus() string  { return "Bellis" }

func testPolymorphismInterface() bool {
	l := new(Lily)
	r := new(Rose)
	d := new(Daisy)
	f := [...]Flower{l, r, d}
	return f[0].Petals() == 3
}

func testEmbeddingInterface() bool {
	l := new(Lily)
	r := new(Rose)
	d := new(Daisy)
	f := [...]Flora{l, r, d}
	return f[0].Petals() == 3
}

func testDowncastInterface() bool {
	l := Lily{}
	var f Flora = l
	return f.Petals() == f.(Flower).Petals()
}
