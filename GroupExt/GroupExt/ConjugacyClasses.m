GroupConjugacyClassRepresentatives[g_?GroupQ] := GroupConjugacyClassRepresentatives[g] = Module[{ret, n, sum, x, k, cent, centorder},
	ret = {GroupIdentity[g]};
	sum = 1;
	k = 1;
	n = GroupOrder[g];
	x = GroupIdentity[g];
	cent = GroupCentralizer2[g, x];		
	centorder = GroupOrder[cent];		
	While[sum < n,
	  	x = GroupElements[cent, {RandomInteger[{1, centorder}]}][[1]];
		cent = GroupCentralizer2[g, x];
		centorder = GroupOrder[cent];		
		Catch[
			Do[If[GroupAreConjugates[g, ret[[i]], x], Throw[True]], {i, 1, k}];
			k = k+1;
			ret = Append[ret, x];
			sum = sum + n/centorder		
		]	 
	];
	ret
]

GroupNumOfConjugacyClasses[g_?GroupQ] := GroupNumOfConjugacyClasses[g] = Length[GroupConjugacyClassRepresentatives[g]]

GroupConjugacyClassSizes[g_?GroupQ] := GroupConjugacyClassSizes[g] = Module[{n},
	n = GroupOrder[g];
	Map[(n/GroupOrder[GroupCentralizer2[g, #]])&, GroupConjugacyClassRepresentatives[g]]
] 

GroupConjugacyClassSize[g_?GroupQ, a_] := GroupConjugacyClassSize[g, a] =
	If[!GroupElementQ[g, a],
		Message[GroupConjugacyClassSize::notelement, a, g];
	, (* else *)	
		GroupOrder[g]/GroupOrder[GroupCentralizer2[g, a]]
	]

SetAttributes[GroupConjugacyClassSize, Listable]

GroupConjugacyClass[g_?GroupQ, a_] :=
	If[!GroupElementQ[g, a],
		Message[GroupConjugacyClass::notelement, a, g];
	, (* else *)	
		Union[a^GroupElements[g]]
	]

GroupConjugacyClassNum[g_, a_] := Module[{classes},
	classes = GroupConjugacyClassRepresentatives[g];
	Do[
		If[GroupAreConjugates[g, a, classes[[i]]],
			Return[i]
		]
	, {i, Length[classes]}]
]	
	
GroupConjugacyClassRepresentative[g_, a_] := GroupConjugacyClassRepresentatives[g][[GroupConjugacyClassNum[g, a]]]
	
GroupConjugacyClassInverses[g_] := Map[GroupConjugacyClassNum[g, #^(-1)]&, GroupConjugacyClassRepresentatives[g]] 	
	
GroupConjugacyClassProductTable[g_] := GroupConjugacyClassProductTable[g] = Module[{repr, i, j, r},
	repr = GroupConjugacyClassRepresentatives[g];
	r = GroupNumOfConjugacyClasses[g];
	Table[GroupConjugacyClassNum[g, repr[[i]]**repr[[j]]], {i, r}, {j, r}]
]

GroupConjugacyClassPower[g_, a_, i_] := Module[{prod, ret, x, j},
	prod = GroupConjugacyClassProductTable[g];
	ret = 1;
	x = a;
	j = i;
	While[j > 0,
		If[Mod[j, 2] == 1, ret = prod[[ret, x]]];
		j = Floor[j/2];
		x = prod[[x, x]]	
	];
	ret
]
