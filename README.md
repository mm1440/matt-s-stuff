Mathematica Package[1]



mma Package:
(* ::Package:: *)

SetDirectory["C:\\Desktop\\WolframFolder"]


(* ::Section:: *)
(*MIDPOINTS ETC.*)
(*Makes: midpoint, vector, ed, midpoint2[{ }], vector2[{ }], ed2[{ }]*)
(**)


HouseholderMatrix[v_?VectorQ]:=IdentityMatrix[Length[v]]-2 Transpose[{v}].{v}/(v.v)


dPcore[L_,p_,n__]:=dPcore[L,p]~Join~Partition[L~Drop~Last@p,n]


dPcore[L_,p_,All]:=dPcore[L,p]~Append~Drop[L,Last@p]


dPcore[L_,p:{q___,_}]:=Inner[L[[#;;#2]]&,{0,q}+1,p,Head@L]


dynamicPartition[L_,p:{__Integer},x___]:=dPcore[L,Accumulate@p,x]/;!Negative@Min@p&&Length@L>=Tr@p


dPartition[list_,parlist_]:=dynamicPartition[list,parlist,All]


midpoint2D[{pt1_,pt2_}]:={.5(pt1[[1]]+pt2[[1]]),.5(pt1[[2]]+pt2[[2]])}


midpoint[pt1_,pt2_]:={(pt1[[1]]+pt2[[1]])/2,(pt1[[2]]+pt2[[2]])/2,(pt1[[3]]+pt2[[3]])/2};


midpoint2[{pt1_,pt2_}]:={(pt1[[1]]+pt2[[1]])/2,(pt1[[2]]+pt2[[2]])/2,(pt1[[3]]+pt2[[3]])/2};


vector[p1_,p2_]:={p2[[1]]-p1[[1]],p2[[2]]-p1[[2]],p2[[3]]-p1[[3]]}


vector2[{p1_,p2_}]:={(p2[[1]]-p1[[1]]),(p2[[2]]-p1[[2]]),(p2[[3]]-p1[[3]])};


vector2d[{p1_,p2_}]:={(p2[[1]]-p1[[1]]),(p2[[2]]-p1[[2]])};


ed[p1_,p2_]:=EuclideanDistance[p1,p2]


ed2[{p1_,p2_}]:=EuclideanDistance[p1,p2]


intersections[{{p1_,q1_},{p2_,q2_}}]:=Module[
{
v1=#/Sqrt[#.#]&[q1-p1],
v2=#/Sqrt[#.#]&[q2-p2],
v12,s1,s2
},
v12=Cross[v1,v2];
s1=Det[{p2-p1,v2,v12}]/v12.v12;
s2=Det[{p2-p1,v1,v12}]/v12.v12;
(p1+p2+v1 s1+v2 s2)/2
] 


PointPlaneDistance[x0_,x_]:=Normalize[Cross[x[[2]]-x[[1]],x[[3]]-x[[1]]]].(x[[1]]-x0)


midpoints3pts[pts_]:=With[{a=midpoint2@pts[[1;;2]],b=midpoint2@pts[[2;;3]],c=midpoint2@pts[[{3,1}]]},{a,b,c}]


midpointsP[pts_]:=Append[Table[midpoint2@pts[[n;;n+1]],{n,1,Length@pts-1,1}],midpoint2@pts[[{Length@pts,1}]]]


curvature[curve_, param_] := 
  ((#1.#1 #2.#2 - (#1.#2)^2)/(#1.#1)^3)& @@ 
                             {D[curve, param], D[curve, {param, 2}]}



PointLineDistance[{x1_,x2_},x0_]:=Norm[Cross[x2-x1,x1-x0]]/Norm[x2-x1]


intersectpts[lines_]:=Table[intersections@lines[[{n,If[n==Length@lines,1,n+1]}]],{n,1,Length@lines,1}]


colorlistn[nn_]:=Table[ColorData["VisibleSpectrum"][n],{n,380,750,370/nn}]


edgefacepts[pts_]:=With[{len=Length@pts},Append[Table[pts[[n;;n+1]],{n,1,len-1,1}],{pts[[len]],pts[[1]]}]]


ggrob[grob_]:=Graphics3D[grob]


listpolys[pts_(* two lists e.g. top and bottom *)]:=Module[{temp1,temp2,temp3,polys},temp1 = RotateRight[pts];
temp2 = Transpose[RotateRight[Transpose[pts]]];
temp3 = RotateRight[temp2];
polys = Drop[MapThread[Polygon[{#1, #2, #3, #4}]&,
                       {pts, temp1, temp3, temp2}, 2], 1]]


vectorangle[pts_]:=VectorAngle[vector2@pts[[1;;2]],vector2@pts[[{3,2}]]]*(180/Pi)


(* ::Section:: *)
(*ARCLENGTH*)
(*Makes: byarclength, lineLength *)
(**)


lineLength[pts_List]:=Total[Apply[EuclideanDistance,Partition[pts,2,1],{1}]];


successiveLengths[pts_List]:=Prepend[Accumulate[Apply[EuclideanDistance,Partition[pts,2,1],{1}]],0.];


byArcLength[pts_List]:=Module[{lngth,withoutDuplicates,succLengths,divisionPointsNo},
lngth=N@lineLength[pts];
withoutDuplicates=Append[Most[Split[pts,lngth+EuclideanDistance[#1,#2]==lngth&][[All,1]]],Last@pts];
succLengths=successiveLengths[withoutDuplicates];
divisionPointsNo=Length[succLengths//.{a___,b_List,b_,c___}:>{a,b,c}];
Function[{t},Evaluate[Through[Map[Interpolation[Transpose[{succLengths,#}]//.({a___List,{b_?NumericQ,c_},{b_,d_},e___}):>{a,{b,c},e},InterpolationOrder->If[divisionPointsNo>1,1,0]]&,Transpose[withoutDuplicates]][t]]]]];


scslenpts[pts_]:=successiveLengths@pts;


alpertablepts[pts_]:=With[{len=lineLength@pts,scs=scslenpts[pts]},Table[scs[[n]]/len,{n,1,Length@pts,1}]];


(* ::Section:: *)
(*CIRCUM*)
(*  Makes: mycircum,toxyn,toxyn2,pointint,circumcirlce,circumC*)
(*  *)


myArc3D[{p1_,p3_,p2_},n_: 2,prim_: Line]:=Module[{\[Alpha],lab,axis,aarc,tm,alpha},lab=m+Norm[a-m]*Normalize[b-m];
axis=(p1-p3)\[Cross](p2-p3);
aarc=(VectorAngle[p1-p3,p2-p3]);
tm=RotationMatrix[alpha,axis];
{prim@Table[p3+tm.(p1-p3),{alpha,0,aarc,aarc/n}],aarc}]


mycircum[pts_]:=Module[{a,d,f,g,center,radius},
a=Det[{{pts[[1]][[1]],pts[[1]][[2]],1},{pts[[2]][[1]],pts[[2]][[2]],1},{pts[[3]][[1]],pts[[3]][[2]],1}}];
d=-1/2 Det[{{pts[[1]][[1]]^2+pts[[1]][[2]]^2,pts[[1]][[2]],1},{pts[[2]][[1]]^2+pts[[2]][[2]]^2,pts[[2]][[2]],1},{pts[[3]][[1]]^2+pts[[3]][[2]]^2,pts[[3]][[2]],1}}];
f=1/2 Det[{{pts[[1]][[1]]^2+pts[[1]][[2]]^2,pts[[1]][[1]],1},{pts[[2]][[1]]^2+pts[[2]][[2]]^2,pts[[2]][[1]],1},{pts[[3]][[1]]^2+pts[[3]][[2]]^2,pts[[3]][[1]],1}}];
g=-Det[{{pts[[1]][[1]]^2+pts[[1]][[2]]^2,pts[[1]][[1]],pts[[1]][[2]]},{pts[[2]][[1]]^2+pts[[2]][[2]]^2,pts[[2]][[1]],pts[[2]][[2]]},{pts[[3]][[1]]^2+pts[[3]][[2]]^2,pts[[3]][[1]],pts[[3]][[2]]}}];
center={-d/a,-f/a,0};
radius=Sqrt[(f^2+d^2)/a^2-g/a];
{center,radius}]


toxyn[pts_]:=Module[{t,r,n,c,ri,ti,vi,v1,d},
t=TranslationTransform[-pts[[2]]][pts];
v1=midpoint[t[[1]],t[[3]]];
r=RotationTransform[{v1,{0,0,1}}][Append[t,v1]]//Chop;
n=Cross[vector[r[[1]],r[[2]]],vector[r[[2]],r[[3]]]];
d=RotationTransform[{n,{0,0,1}}][r]//Chop;
c=mycircum[d];
ri=RotationTransform[{{0,0,1},n}][c[[1]]];
vi=RotationTransform[{{0,0,1},v1}][ri];
ti=TranslationTransform[pts[[2]]][vi];
{ti,c[[2]]}];


toxyn2[pts_]:=Module[{t,r,n,c,ri,ti,vi,v1,d},
t=TranslationTransform[-pts[[2]]][pts];
v1=midpoint[t[[1]],t[[3]]];
r=RotationTransform[{v1,{0,1,0}}][Append[t,v1]]//Chop;
n=Cross[vector[r[[1]],r[[2]]],vector[r[[2]],r[[3]]]];
d=RotationTransform[{n,{0,0,1}}][r]//Chop;
c=mycircum[d];
ri=RotationTransform[{{0,0,1},n}][c[[1]]];
vi=RotationTransform[{{0,0,1},v1}][ri];
ti=TranslationTransform[pts[[2]]][vi];
{ti,c[[2]]}]


pointsint[func_,t_,int_]:={func[t-int],func[t],func[t+int]}


circumcircle[pts_]:=Module[{a,b,c,d,e},
a=toxyn[pts];
b=vector[pts[[1]],a[[1]]];
c=vector[pts[[2]],a[[1]]];
d=Cross[b,c];
e=Table[RotationTransform[t,d,a[[1]]][pts[[2]]],{t,0,2Pi,2Pi/40}];
Line@e]


movepttocenter[pts_,no_,t_]:=Module[{a,b,c,d,e,f},
a=toxyn[pts];
b=a[[1]];
c=pts[[no]];
d=(1-t)c+t b;
Point@{b,d}]



movepttocenter2[pts_,no_,t_]:=Module[{a,b,c,d,e,f},
a=toxyn[pts];
b=a[[1]];
c=pts[[no]];
d=(1-t)c+t b
]



movepttocenterdis[pts_,no_,distance_]:=Module[{a,b,c,d,e,f},
a=toxyn[pts];
b=a[[1]];
c=pts[[no]];
d=Catch[Table[If[EuclideanDistance[(1-tt)c+tt b,c]>distance,Throw[(1-tt)c+tt b],{}],{tt,0,1,.001}]]
]


movepttocenterdisSlow[pts_,no_,distance_]:=Module[{a,b,c,d,e,f},
a=toxyn[pts];
b=a[[1]];
c=pts[[no]];
d=Catch[Table[If[EuclideanDistance[(1-tt)c+tt b,c]>distance,Throw[(1-tt)c+tt b],{}],{tt,0,1,.00001}]]
]


circumC[pts_]:={circumcircle[pts],toxyn[pts]}


cross3[list_]:=Cross[vector2@list[[1;;2]],vector2@list[[2;;3]]]


crosscenter[list_]:=With[{centerpt=toxyn[list][[1]]},Cross[vector2@{list[[1]],centerpt},vector2@{list[[3]],centerpt}]]


crosscentervec[list_]:=With[{centerpt=toxyn[list][[1]]},vector2@{centerpt,Cross[vector2@{list[[1]],centerpt},vector2@{list[[3]],centerpt}]}]



(*GCOMPLEX*)


newrows[1]={1,2,1};


Do[newrows[i]={(newrows[i-1][[2]]-newrows[i-1][[3]])+newrows[i-1][[1]],2i+1,i,newrows[i-1][[1]]+newrows[i-1][[2]]+1},{i,2,150,1}]


rownumbers[1]={1,1};


Do[rownumbers[i]={(newrows[i-1][[2]]-newrows[i-1][[3]])+newrows[i-1][[1]],newrows[i-1][[1]]+newrows[i-1][[2]]+1},{i,2,150,1}]


rownumbers2[n_]:=With[{pts1=rownumbers[n][[1]],pts2=rownumbers[n][[2]]},Table[nn,{nn,pts1,pts2,1}]]


gclist[r1_]:=Module[{a,b,c,e2,d,e,f,g},
a=rownumbers2[r1];
b=rownumbers2[r1+1];
e=Reverse@b;
e2=Reverse@a;
c=-2+Length@a+Length@b;
d=Table[{a[[n]],b[[n]],b[[n+1]]},{n,1,Length@b-1,1}];
f=Table[{a[[n]],a[[n+1]],b[[n+1]]},{n,1,Length@b-2,1}];
Quiet@Union@Flatten[{d,f},1]]


grclisttri[rownumber_]:=If[rownumber==1,{{1,2,3},{1,3,4}},gclist[rownumber]]


gcomplextri[numberofrows_]:=Flatten[Table[grclisttri[n],{n,1,numberofrows,1}],1]


gclistquad[lno_]:=Table[{n,n+1,n+2,n+3},{n,1,lno^2*4,4}]


gcomplexquad[lno_]:=Table[{n,n+1,n+2,n+3},{n,1,lno^2*4,4}]


tripos[side_][n_][p1_,p2_,p3_][lno_]:=Module[{psec,lineL,alf,alftable,across},
psec[1]=Reverse@ptstable[side][n][[p1;;p2]];
psec[2]=ptstable[side][n][[p2;;p3]];
Do[lineL[i]=lineLength@psec[i],{i,1,2,1}];
Do[alf[i]=byArcLength@psec[i],{i,1,2,1}];
Do[alftable[i]=Table[alf[i][s],{s,lineL[i],0,-lineL[i]/(lno)}],{i,1,2,1}];
Do[across[1][nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno+2-nn)}],{nn,1,lno,1}];
Prepend[Flatten[Reverse@Table[across[1][nn],{nn,1,lno,1}],1],ptstable[side][n][[p2]]]]


trilist[list1_,list2_,point_][lno_]:=Module[{psec,lineL,alf,alftable,across},
psec[1]=Reverse@Partition[Flatten[list1],3];
psec[2]=Partition[Flatten[list2],3];
Do[lineL[i]=lineLength@psec[i],{i,1,2,1}];
Do[alf[i]=byArcLength@psec[i],{i,1,2,1}];
Do[alftable[i]=Table[alf[i][s],{s,lineL[i],0,-lineL[i]/(lno)}],{i,1,2,1}];
Do[across[1][nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno+2-nn)}],{nn,1,lno,1}];
Prepend[Flatten[Reverse@Table[across[1][nn],{nn,1,lno,1}],1],point]]



trilistout[list1_,list2_,point_][lno_]:=Module[{psec,lineL,alf,alftable,across},
psec[1]=Reverse@Partition[Flatten[list1],3];
psec[2]=Partition[Flatten[list2],3];
Do[lineL[i]=lineLength@psec[i],{i,1,2,1}];
Do[alf[i]=byArcLength@psec[i],{i,1,2,1}];
Do[alftable[i]=Table[alf[i][s],{s,lineL[i],0,-lineL[i]/(lno)}],{i,1,2,1}];
Do[across[1][nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno+2-nn)}],{nn,1,lno,1}];
alftable[#]&/@Range[2]]



quadlist[list1_,list2_][lno_]:=Module[{a,io,inpoints,mmpts,across,along,len,alf,alftable,psec,verts1,verts2,vertloc1,vertloc2},
psec[1]=list1;
psec[2]=list2;
Do[len[nn]=lineLength@psec[nn],{nn,1,4,1}];
Do[alf[i]=byArcLength[psec[i]],{i,1,4,1}];
Do[alftable[i]=Table[alf[i][s],{s,0,len[i],len[i]/lno}],{i,1,4,1}];
Do[along[nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno)}],{nn,1,lno+1,1}];
vertloc1=
Table[{along[nn][[mm]],along[nn][[mm+1]],along[nn+1][[mm+1]],along[nn+1][[mm]]},{nn,1,lno,1},{mm,1,lno,1}];
Partition[Flatten[vertloc1],3]
]


quadlist2[list1_,list2_][lno_][mno_]:=Module[{a,io,inpoints,mmpts,across,along,len,alf,alftable,psec,verts1,verts2,vertloc1,vertloc2},
psec[1]=list1;
psec[2]=list2;
Do[len[nn]=lineLength@psec[nn],{nn,1,4,1}];
Do[alf[i]=byArcLength[psec[i]],{i,1,4,1}];
Do[alftable[i]=Table[alf[i][s],{s,0,len[i],len[i]/mno}],{i,1,4,1}];
Do[along[nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno)}],{nn,1,mno+1,1}];
vertloc1=
Table[{along[nn][[mm]],along[nn][[mm+1]],along[nn+1][[mm+1]],along[nn+1][[mm]]},{nn,1,mno,1},{mm,1,lno,1}];
Partition[Flatten[vertloc1],3]
]


quadlistout[list1_,list2_][lno_]:=Module[{a,io,inpoints,mmpts,across,along,len,alf,alftable,psec,verts1,verts2,vertloc1,vertloc2},
psec[1]=list1;
psec[2]=list2;
Do[len[nn]=lineLength@psec[nn],{nn,1,4,1}];
Do[alf[i]=byArcLength[psec[i]],{i,1,4,1}];
Do[alftable[i]=Table[alf[i][s],{s,0,len[i],len[i]/lno}],{i,1,4,1}];
Do[along[nn]=Table[(1-t)alftable[1][[nn]]+t alftable[2][[nn]],{t,0,1,1/(lno)}],{nn,1,lno+1,1}];
vertloc1=
Table[{along[nn][[mm]],along[nn][[mm+1]],along[nn+1][[mm+1]],along[nn+1][[mm]]},{nn,1,lno,1},{mm,1,lno,1}];
Partition[Flatten[vertloc1],3];alftable[#]&/@Range[2]
]


quadlistgrob[list1_,list2_][lno_]:={GraphicsComplex[quadlist[list1,list2][lno],Polygon@#&@gcomplexquad[lno]]}


trilistgrob[list1_,list2_,point_][lno_]:={GraphicsComplex[trilist[list1,list2,point][lno],Polygon@#&@gcomplextri[lno]]}


trigrob[pts_][lno_]:=GraphicsComplex[pts,Polygon@#&@gcomplextri[lno]]


quadgrob[pts_][lno_]:=GraphicsComplex[pts,Polygon@#&@gcomplexquad[lno]]


quadgrob2[pts_]:=With[{polylist=Partition[pts,4],verts=Union@Flatten[Partition[pts,4],1]},Module[{a,b,c},a=Table[Flatten[First[Position[verts,polylist[[n]][[#]]]]&/@Range[4]],{n,1,Length@polylist,1}];GraphicsComplex[verts,Polygon@a]]]


(* ::Section:: *)
(*FRENET FRAME*)


 tangent[alpha_][t_]:= D[alpha[tt],tt]/
        Simplify[Factor[D[alpha[tt],tt].
          D[alpha[tt],tt]]]^(1/2)  /. tt->t


binormal[alpha_][t_]:=Simplify[Cross[D[alpha[tt],tt],D[alpha[tt],{tt,2}]]]/Simplify[Factor[Cross[D[alpha[tt],tt],D[alpha[tt],{tt,2}]].Cross[D[alpha[tt],tt],D[alpha[tt],{tt,2}]]]]^(1/2)/.tt->t



 normal[alpha_][t_]:= Cross[binormal[alpha][t],
                           tangent[alpha][t]]


frenetframe[alpha_][t_]:=        {Line[{alpha[t],alpha[t] + tangent[alpha][t]}],         Line[{alpha[t],alpha[t] + normal[alpha][t]}],         Line[{alpha[t],alpha[t] + binormal[alpha][t]}]}



fframegrobr[t_]:=frenetframe[r][t]


drfunc[func_][t_]:=D[func[tt],tt]/.tt->t


ddrfunc[func_][t_]:=D[func[tt],{tt,2}]/.tt->t


tanfunc[func_][t_]:=With[{a=drfunc[func][t]},a/Sqrt[a.a]]


bnormfunc[func_][t_]:=Evaluate@With[{a=Cross[drfunc[func][t],ddrfunc[func][t]]},a/Sqrt[a.a]]


normfunc[func_][t_]:=Cross[tanfunc[func][t],bnormfunc[func][t]]


dtanLfunc[func_][t_,inc_]:=vector2@{func[t],func[t-inc]}


R1func[func_][n_ (*secs*)]:=HouseholderMatrix[dtanLfunc[func][n secs,secs]];


R2func[func_][n_]:=N@HouseholderMatrix[tanfunc[func][n secs]-R1func[func][n].tanfunc[func][(n-1)secs]]


(* ::Section::Closed:: *)
(*MINMAXPOINTS*)


maximay[points_]:=1+Position[Differences[Sign[Differences[points[[All,2]]]]],-2]


minimay[points_]:=1+Position[Differences[Sign[Differences[points[[All,2]]]]],2]


maximax[points_]:=1+Position[Differences[Sign[Differences[points[[All,1]]]]],-2]


minimax[points_]:=1+Position[Differences[Sign[Differences[points[[All,1]]]]],2]


maximaz[points_]:=1+Position[Differences[Sign[Differences[points[[All,3]]]]],-2]


minimaz[points_]:=1+Position[Differences[Sign[Differences[points[[All,3]]]]],2]


minmaxpointsPos[pts_]:=Union@Flatten@{minimay[pts],maximay[pts],minimax[pts],maximax[pts],minimaz[pts],maximaz[pts]}


minmaxpointsposx[pts_]:=Union@Flatten@{minimax[pts],maximax[pts]}


minmaxpointsposy[pts_]:=Union@Flatten@{minimay[pts],maximay[pts]}


minmaxpointsposz[pts_]:=Union@Flatten@{minimaz[pts],maximaz[pts]}


minmaxpointsAll[pts_]:=pts[[#]]&@Union@Flatten@{minimay[pts],maximay[pts],minimax[pts],maximax[pts],minimaz[pts],maximaz[pts]}


minmaxpointsx[pts_]:=pts[[#]]&@Union@Flatten@{minimax[pts],maximax[pts]}


minmaxpointsy[pts_]:=pts[[#]]&@Union@Flatten@{minimay[pts],maximay[pts]}


minmaxpointsz[pts_]:=pts[[#]]&@Union@Flatten@{minimaz[pts],maximaz[pts]}


minmaxpointspos[pts_]:=Union@Flatten@{minimay[pts],maximay[pts],minimax[pts],maximax[pts]}


minmaxpoints2[pts_]:=pts[[#]]&@Union@Flatten@{minimay[pts],maximay[pts],minimax[pts],maximax[pts]}


(* ::Section:: *)
(*POLYROT*)


rint[r_]:=1+RandomInteger[r-1]




netlists[number_]:=Union@Sort@Table[With[{pts=flatlist},{Length@pts,pts}],{number}]


SignedArea[p1_,p2_,p3_]:=0.5 (#1[[2]] #2[[1]]-#1[[1]] #2[[2]])&[p2-p1,p3-p1];


IntersectionQ[p1_,p2_,p3_,p4_]:=SignedArea[p1,p2,p3] SignedArea[p1,p2,p4]<0&&SignedArea[p3,p4,p1] SignedArea[p3,p4,p2]<0;


Deintersect[p_]:=Append[p,p[[1]]]//.{s1___,p1_,p2_,s2___,p3_,p4_,s3___}/;IntersectionQ[p1,p2,p3,p4]:>({s1,p1,p3,Sequence@@Reverse@{s2},p2,p4,s3})//Most;


transface[pts_]:=Quiet@Chop@Module[{a,b,c,d,e},
a=toxyn[midpointsP[pts][[1;;3]]][[1]];
b=TranslationTransform[-a][pts];
c=RotationTransform[{b[[1]],{1,0,0}}][b];
d=midpointsP[c][[1;;2]];
e=With[{cr=Cross[d[[1]],d[[2]]]},RotationTransform[{cr,{0,0,1}}][c]]
]


transface2[pts_]:=Quiet@Chop@Module[{a,b,btrans,ctrans,dtrans,etrans,c,d,e,f},
a=toxyn[midpointsP[pts][[1;;3]]][[1]];
b=TranslationTransform[-a][pts];
btrans=TranslationTransform[-a];
c=RotationTransform[{b[[1]],{1,0,0}}][b];
ctrans=RotationTransform[{b[[1]],{1,0,0}}];
d=midpointsP[c][[1;;2]];
e=With[{cr=Cross[d[[1]],d[[2]]]},RotationTransform[{cr,{0,0,-1}}]];
Composition[e,ctrans,btrans]]


transfaceedge[pts_][edgeno_]:=Quiet@Chop@Module[{a,b,c,d,e,f,g,h},
f=midpoint2@pts[[If[edgeno==Length@pts,{Length@pts,1},{edgeno,edgeno+1}]]];
a=toxyn[midpointsP[pts][[1;;3]]][[1]];
b=TranslationTransform[-a][Append[pts,f]];
c=RotationTransform[{b[[1]],{1,0,0}}][b];
d=midpointsP[c][[1;;2]];
e=With[{cr=Cross[d[[1]],d[[2]]]},RotationTransform[{cr,{0,0,1}}][c]];
g=RotationTransform[{Last@e,{0,1,0}}][e]
]


(* ::Subsection:: *)
(*MAXRADIUS*)
(*  needs: rtable, tanvectable*)





(* ::Subsection:: *)
(*TwoStuff*)


secs=N@2Pi/400;


scslenpts[pts_]:=successiveLengths@pts;


alpertablepts[pts_]:=With[{len=lineLength@pts,scs=scslenpts[pts]},Table[scs[[n]]/len,{n,1,Length@pts,1}]];


dtanLfunc[func_][t_,inc_]:=vector2@{func[t],func[t-inc]}


(*change R!, put in inc *)


R1func[func_][n_ (*secs*)]:=HouseholderMatrix[dtanLfunc[func][n secs,secs]];





colorlist={Red,Yellow,Purple,Green,Blue,Pink,Orange};


polygrob[pts_]:=Module[{len,nos,colors,c,d,e},
len=Length@pts;
nos=Length@pts[[1]]-1;
colors=If[nos<=7,colorlist,colorlistn[nos]];
c=Table[Table[{pts[[n]][[i]],pts[[n]][[i+1]],pts[[n+1]][[i+1]],pts[[n+1]][[i]]},{i,1,nos,1}],{n,1,len-1}];
Table[{colors[[i]],Polygon@c[[All,i]]},{i,1,nos,1}]]


ttable=Range[0,2Pi,secs];


Do[rmfint[xyz]=Hold[With[{table=rmftablefunc[r,secs]},Interpolation[Partition[Riffle[ttable,table[[All,xyz]]],2]]],{xyz,1,3,1}];
myrmf[t_]:=Table[rmfint[xyz][t],{xyz,1,3,1}]]









End mmaPackage[1]


RhinoScript[1]: Imports folder into Rhino, will add Python script at bottom.


 Option Explicit
 
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 ' BatchConvert3DMtoIGES
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 Sub BatchConvert3DMtoIGES()
 
   ' Make sure RhinoScript does not reinitialize when opening models,
   ' otherwise this script will only process one file.
   Rhino.Command "_-Options _RhinoScript _Reinitialize=_No _Enter _Enter", 0
 
   ' Allow the user to interactively pick a folder
   Dim sFolder
   sFolder = Rhino.BrowseForFolder(, "Select folder to process", "BatchConvert3DMtoIGES")
   If VarType(sFolder) <> vbString Then Exit Sub
 
   ' Create a file system object
   Dim oFSO
   Set oFSO = CreateObject("Scripting.FileSystemObject") 

   ' Get a folder object based on the selected folder
   Dim oFolder
   Set oFolder = oFSO.GetFolder(sFolder)
 
   ' Process the folder
   ProcessFolder oFSO, oFolder
 
   ' Release the objects
   Set oFolder = Nothing
   Set oFSO = Nothing
 
   ' Close the last file processed
   Rhino.DocumentModified False
   Rhino.Command "_-New _None", 0
 
 End Sub
 
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 ' ProcessFolder
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 Sub ProcessFolder(oFSO, oFolder)
 
   ' Process all .dwg files in the selected folder
   Dim oFile, strOpen, strSave
   For Each oFile In oFolder.Files
     If LCase(oFSO.GetExtensionName(oFile.Path)) = "3dm" Then
       strOpen = LCase(oFile.Path)
       strSave = LCase(Replace(strOpen, ".3dm", ".iges", 1, -1, 1))
       ProcessFile strOpen, strSave
     End If
   Next
 
   ' Comment out the following lines if you do not
   ' want to recursively process the selected folder.
   Dim oSubFolder
   For Each oSubFolder In oFolder.SubFolders
     ProcessFolder oFSO, oSubFolder
   Next
 
 End Sub 
 
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 ' ProcessFile
 '''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
 Sub ProcessFile(strOpen, strSave)
   Rhino.DocumentModified False
   Rhino.Command "_-Open " & Chr(34) & strOpen & Chr(34), 0
   Rhino.Command "_-Zoom _All _Extents", 0
   Rhino.Command "_-SetActiveView _Top", 0
   Rhino.Command "_-Save " & Chr(34) & strSave & Chr(34), 0
 End Sub



