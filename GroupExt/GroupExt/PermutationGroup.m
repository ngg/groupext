ClearAttributes[NonCommutativeMultiply, Protected]
NonCommutativeMultiply[x_Cycles, y_Cycles] := PermutationProduct[x, y]

ClearAttributes[Power, Protected]
Power[x_Cycles, n_Integer] := PermutationPower[x, n]
Power[n_Integer, a_Cycles] := PermutationReplace[n, a]
Power[n_Integer, g_?PermutationGroupQ] := GroupOrbits[g, {n}][[1]]
Power[x_Cycles, y_Cycles] := y^(-1)**x**y

PermutationGroupQ[g_] := False
PermutationGroupQ[g_] := True /; MemberQ[{
	PermutationGroup, GroupStabilizer, GroupSetwiseStabilizer, GroupCentralizer,
	SymmetricGroup, AlternatingGroup, CyclicGroup, AbelianGroup,
	DihedralGroup, MathieuGroupM11, MathieuGroupM12, MathieuGroupM22,
	MathieuGroupM23, MathieuGroupM24, JankoGroupJ1, JankoGroupJ2,
	JankoGroupJ3, JankoGroupJ4, HigmanSimsGroupHS, ConwayGroupCo1,
	ConwayGroupCo2, ConwayGroupCo3, McLaughlinGroupMcL, SuzukiGroupSuz,
	HeldGroupHe, RudvalisGroupRu, FischerGroupFi22, FischerGroupFi23,
	FischerGroupFi24Prime, TitsGroupT, ONanGroupON, HaradaNortonGroupHN,
	ThompsonGroupTh, LyonsGroupLy, BabyMonsterGroupB, MonsterGroupM
	}, Head[g]]

GroupQ[g_?PermutationGroupQ] := True
	
PermutationGroupElementFromImage[g_?PermutationGroupQ, a_Integer, b_Integer] := Module[{lk = 1, ln = 1, sn, s = GroupGenerators[g], l = {Cycles[{}] -> a}, c, x, i},
	Catch[
		sn = Length[s];
		While[lk <= ln,
			Do[
	 			c = l[[lk, 1]] ** s[[i]];
				x = l[[lk, 2]]^s[[i]];
				If[x == b, Throw[c]];
				If[Position[l, x, 2] == {},
					l = Append[l, c -> x];
					ln = ln + 1
				]
			,{i, sn}];
			lk = lk + 1
		];
		Null
	]
]
	
PermutationGroupElementFromBaseImages[sc_, base_, basen_, img_] := Module[{i, x, ret = Cycles[{}]},
	Catch[
		Do[
			If[!NullQ[img[[i]]],
				x = PermutationGroupElementFromImage[sc[[i,2]], base[[i]], img[[i]]^(ret^(-1))];
				If[NullQ[x], Throw[Null]];
				ret = x**ret
			]
		,{i, basen}];	
		ret
	]
]

PermutationGroupElementFromImages[g_?PermutationGroupQ, s_] := Module[{sc, wantedbase, base, basen, ret, i, x},
	Catch[
		wantedbase = Map[First, s];
		sc = GroupStabilizerChain[g, GroupActionBase -> wantedbase];
		basen = Position[sc, PermutationGroup[{}]][[1, 1]] - 1;
		base = sc[[basen + 1, 1]];
		ret = PermutationGroupElementFromBaseImages[sc, base, basen, Map[(x = Position[wantedbase, #]; If [Length[x] == 0, Null, s[[x[[1,1]], 2]]])&, base]];
		If[NullQ[ret], Throw[Null]];
		Do[If[s[[i, 1]]^ret != s[[i, 2]], Throw[Null]], {i,1,Length[s]}];
		ret
	]
]

PermutationGroupAreConjugatesBT[a_, b_, sc_, base_, cangoto_, follow_, img_] := Module[{e, imgn, newimg = img, basen, i, next},
	Catch[
		imgn = Length[newimg];
		basen = Length[base];
		While[imgn < basen && follow[[imgn+1]],
			next = newimg[[imgn]]^b;
			If [Position[newimg, next, 1] != {}, Throw[False]];
			newimg = Append[newimg, next];
			imgn = imgn + 1;
		];
		If[imgn == basen,
			e = PermutationGroupElementFromBaseImages[sc, base, basen, newimg];
			If[!NullQ[e] && a^e == b, True, False]
		, (* else *)
			Catch[		
				Do[
					next = cangoto[[imgn+1, i]];
					If [Position[newimg, next, 1] == {},
						If[PermutationGroupAreConjugatesBT[a, b, sc, base, cangoto, follow, Append[newimg, next]] == True, Throw[True]];
					];
				,{i,Length[cangoto[[imgn+1]]]}];
				False
			]
		]
	]
]

PermutationGroupAreConjugates[g_, a_, b_] := Module[{as, bs, i, sc, basen, base, cangoto, follow, pos, bcyclelen, set, len},
	Catch[
		set = Union[Flatten[Map[#[[1]] &, GroupGenerators[g]]]];
		as = Sort[a[[1]], (Length[#1] > Length[#2]) &];
		bs = Sort[b[[1]], (Length[#1] > Length[#2]) &];
		If[Map[Length, as] != Map[Length, bs], Throw[False]];

 		sc = GroupStabilizerChain[g, GroupActionBase -> Flatten[as]];		
		basen = Position[sc, PermutationGroup[{}]][[1, 1]] - 1;	
		sc = sc[[1 ;; basen + 1]];
		base = sc[[basen + 1, 1]];
		follow = Table[i > 1 && base[[i-1]]^a == base[[i]], {i, basen}];

		bcyclelen = Table[pos = Position[bs, set[[i]]]; If[pos == {}, 1, Length[bs[[pos[[1, 1]]]]]], {i, Length[set]}];
		
		cangoto = Table[
			pos = Position[as, base[[i]]];
			len = If[pos == {}, 1, Length[as[[pos[[1, 1]]]]]];
			Select[GroupOrbits[g, {base[[i]]}][[1]], (bcyclelen[[#]] == len)&]
		, {i, basen}];		

		PermutationGroupAreConjugatesBT[a, b, sc, base, cangoto, follow, {}]
	]
]

GroupAreConjugates[g_?PermutationGroupQ, a_Cycles, b_Cycles] := 
	If[!GroupElementQ[g, a],
		Message[GroupAreConjugates::notelement, a, g];
		If[!GroupElementQ[g, b],
			Message[GroupAreConjugates::notelement, b, g];
		];
	, (* else *)
		If[!GroupElementQ[g, b],
			Message[GroupAreConjugates::notelement, b, g];
		, (* else *)	
			PermutationGroupAreConjugates[g, a, b]
		]
	]	
  	
GroupIdentity[g_?PermutationGroupQ] := Cycles[{}]  	

GroupElementOrder[g_?PermutationGroupQ, a_] :=
	If[!GroupElementQ[g, a],
		Message[GroupElementOrder::notelement, a, g];
	, (* else *)	
		PermutationOrder[a]
	]

  	