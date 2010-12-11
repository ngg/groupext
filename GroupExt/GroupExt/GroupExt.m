BeginPackage["GroupExt`"]

NullQ::usage = ""
SubspaceIntersection::usage = ""

GroupQ::usage = "GroupQ[g] determines whether g is a group or not."
GroupIdentity::usage = ""
GroupElementOrder::usage = ""
GroupExponent::usage = ""
GroupCentralizer2::usage = "bugfix"
GroupAreConjugates::usage = ""
GroupConjugacyClass::usage = ""
GroupConjugacyClassRepresentatives::usage = ""
GroupNumOfConjugacyClasses::usage = ""
GroupConjugacyClassSizes::usage = ""
GroupConjugacyClassSize::usage = ""
GroupConjugacyClassRepresentative::usage = ""
GroupCharacterTable::usage = ""
GroupCharacterScalarProduct::usage = ""

PermutationGroupQ::usage = "PermutationGroupQ[g] determines whether g is a group or not."
PermutationGroupElementFromImage::usage = ""
PermutationGroupElementFromImages::usage = 

Begin["GroupExt`Private`"]

General::notelement = "`1` is not element of `2`"

NullQ[x_] := ToString[x] == "Null" && !StringQ[x]

GroupQ[g_] := False

GroupCentralizer2[g_?GroupQ, x_] := If[GroupIdentity[g] == x, g, GroupCentralizer[g, x]] 

Get["GroupExt/PermutationGroup.m"]
Get["GroupExt/ConjugacyClasses.m"]
Get["GroupExt/CharacterTable.m"]
Get["GroupExt/LinearAlgebra.m"]

End[]
EndPackage[]

