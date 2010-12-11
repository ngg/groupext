SubspaceIntersection[a_, b_, opts___] := Module[{x},
	
	If[Length[a] == 0 || Length[b] == 0, Return[{}]];
	x = NullSpace[Union[NullSpace[a, opts], NullSpace[b, opts]], opts];
	If[Length[x] == 0, Return[{}]];
	RowReduce[x, opts]
]

Options[SubspaceIntersection] = {Modulus -> 0}
 