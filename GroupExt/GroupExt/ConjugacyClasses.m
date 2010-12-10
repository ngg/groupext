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

GroupConjugacyClassSize[g_?GroupQ, a_] := GroupConjugacyClassSize[g, a] =
	If[!GroupElementQ[g, a],
		Message[GroupConjugacyClassSize::notelement, a, g];
	, (* else *)	
		GroupOrder[g]/GroupOrder[GroupCentralizer[g, a]]
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
	