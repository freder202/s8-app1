//////////////////////////////////////////////////////////////////////
// Author  :    Marc-Andre Tetrault
// Project :    Verification Primer
//
// Universite de Sherbrooke
//////////////////////////////////////////////////////////////////////

class WaveFormControl
	logic enable;
	rand local integer Phase;
	rand local integer Period; // other way to have auto randomization
	local logic [3:0] type; // local same as private
	rand local logic [3:0] len;
	rand logic [7:0] test_string[]; // non-fixed size
	input logic [3:0] wavetype;

	// explicit asdfa
	function new(input logic [3:0] wavetype); // if no decleration,
											 // you'll get autogen'd one

	// call parent constructor, if inherited class
	// super.new(args);
		type= 2'b1;
		Phase = $urandom;
		this.wavetype = wavetype; // usually pretty much used in constructors, rarely in other places.
	endfunction

	contraint etiquette {
		test_string.size() == len; // sinon changera pas, en plus
		// les .size() sont random en premier, (sinon chiant!)
	}

	// contraintes de base, on peut resserrer avec un with
	constraint etiquette2 {
		Phase > 10;
		Phase <= 1_000_000;
	}

	function void print();
		$display("vars are ");
	endfunction

	function void post_randomize(); //
		do_data_integrity();
		do_many_urandoms();
	endfunction

	// function randomize --> built-in function, no possible to override
	// rondomize return 1 if solver failed to follow contraints
	// also has pre-randomize();

	// not possible to overload the function signatures
endclass

// subclass can be used to extend constraints
// parent class needs to declare variables as protected instead of local
// like C++
class subclassType extends WaveFormControl;
	// declare constructor
	function new(input chose);
		super.new(chose);
	endfunction
endclass

WaveFormControl example = new(.wavetype(4'h3));

initial begin
	example.randomize() with {Period>100_000; Period < 1_000_000};

	// example, mais normlameent dans la classe
	// chaque point a N chances d'être pris.
	// total 40*4 + 10*6
	example.randomize() with {Period dist { [10:49] := 4,
											[50:59] := 6
											};
										};

	// le range a 4 chances/6 chances d'être pris, total 10
	example.randomize() with {Period dist { [100_000:500_000] /= 4,
											[500_000:1_000_000] /= 6
											};
										};
end
