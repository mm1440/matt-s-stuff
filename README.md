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


divideTablePos[pts_]:=Module[{sectionnumbersz,sectionnumbers2z,section,len,snlen,c},
len=Length@pts;
sectionnumbersz=Sort@Flatten@{1,minimaz@pts,maximaz@pts,len};
snlen=Length@sectionnumbersz;
sectionnumbers2z=Table[If[n>1,{sectionnumbersz[[n]],sectionnumbersz[[n+1]]},{sectionnumbersz[[n]],sectionnumbersz[[n+1]]}],{n,1,Length@sectionnumbersz-1,1}];
section[1]=With[{start=Last[sectionnumbers2z][[1]],end=sectionnumbers2z[[1]][[2]]},Table[1+Mod[n-1,len-1],{n,start,len+end-1,1}]];
Do[section[n]=Range[#[[1]],#[[2]]]&@sectionnumbers2z[[n]],{n,2,snlen-1,1}];
Table[section[n],{n,1,snlen-2,1}]]


divideTableNos[pts_]:=Module[{sectionnumbersz,sectionnumbers2z,section,len,snlen,c},
len=Length@pts;
sectionnumbersz=Sort@Flatten@{1,minimaz@pts,maximaz@pts,len};
snlen=Length@sectionnumbersz;
sectionnumbers2z=Table[If[n>1,{sectionnumbersz[[n]],sectionnumbersz[[n+1]]},{sectionnumbersz[[n]],sectionnumbersz[[n+1]]}],{n,1,Length@sectionnumbersz-1,1}];
section[1]=With[{start=Last[sectionnumbers2z][[1]],end=sectionnumbers2z[[1]][[2]]},Table[1+Mod[n-1,len-1],{n,start,len+end-1,1}]];
Do[section[n]=Range[#[[1]],#[[2]]]&@sectionnumbers2z[[n]],{n,2,snlen-1,1}];
Table[rtable[[#]]&/@section[n],{n,1,snlen-2,1}]]


(* ::Section:: *)
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


flatlist:=Module[{netlist,flist,c,d,e},
netlist[1]=With[{rnd1=rint[faceno]},{rnd1,list[[rnd1]],newlist=DeleteCases[list,rnd1,2]}];
Do[netlist[n]=Quiet@With[{nlist=netlist[n-1][[3]],rnd2=rint[Length@netlist[n-1][[2]]],facelist=netlist[n-1][[2]]},{facelist[[rnd2]],newlist[[facelist[[rnd2]]]],newlist=DeleteCases[newlist,facelist[[rnd2]],2]}],{n,2,faceno,1}];
flist=Flatten@Table[If[IntegerQ[netlist[n][[1]]]==True,netlist[n][[1]],{}],{n,1,faceno,1}];If[Length@flist!=Length@Union@flist,Rest@flist,flist]]



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


maxradius[rtable_,tanvectable_]:=Module[{vectorxy,dottable1,possiblepts,minkpoints,sort1,mindis,mindislinenos,mindistance,mink,maxradpos,maxrad},
Do[vectorxy[i][j]=vector2@{rtable[[i]],rtable[[j]]},{i,1,tablelength,1},{j,1,tablelength,1}];
Do[dottable1[i]=N@Take[Sort[Table[{i,j,N@Abs[tanvectable[[i]].vectorxy[i][j]]},{j,1,tablelength,1}],#1[[3]]<#2[[3]]&],10],{i,1,tablelength,1}];
possiblepts=Sort[Table[If[i==1,dottable1[i][[3]],dottable1[i][[3]]],{i,1,tablelength-1,1}],#1[[3]]<#2[[3]]&];
minkpoints=Sort[Table[{i,toxyn[rtable[[i-1;;i+1]]][[2]]},{i,2,tablelength-1,1}],#1[[2]]<#2[[2]]&];
sort1=Sort[Table[{possiblepts[[i]][[1;;2]],ed2@rtable[[possiblepts[[i]][[1;;2]]]]},{i,1,tablelength-1,1}],#1[[2]]<#2[[2]]&];
mindis=Max@Table[ed2@rtable[[i;;i+1]],{i,1,tablelength-1,1}];
mindislinenos=Catch[Table[If[sort1[[i]][[2]]>mindis,Throw[sort1[[i]][[1]]]],{i,1,tablelength-1,1}]];
mindistance=ed2@rtable[[mindislinenos]]//N;
mink=minkpoints[[1]][[2]];
maxradpos=With[{a=mink,b=mindistance/2},If[a>b,{b,ToString["distance"]},{minkpoints[[1]][[2]],ToString["curvature"]}]];
maxrad=maxradpos]


(* ::Subsection:: *)
(*TwoStuff*)


secs=N@2Pi/400;


scslenpts[pts_]:=successiveLengths@pts;


alpertablepts[pts_]:=With[{len=lineLength@pts,scs=scslenpts[pts]},Table[scs[[n]]/len,{n,1,Length@pts,1}]];


dtanLfunc[func_][t_,inc_]:=vector2@{func[t],func[t-inc]}


(*change R!, put in inc *)


R1func[func_][n_ (*secs*)]:=HouseholderMatrix[dtanLfunc[func][n secs,secs]];


R2func[func_][n_]:=N@HouseholderMatrix[tanfunc[func][n secs]-R1func[func][n].tanfunc[func][(n-1)secs]]


rmftablefunc[func_,inc_,sign_:1]:=Module[{rtable,tantable,scslengths,linelength,alpertable,tablelength,newnorm2,R1table,R2table,newline,newvec,vecdiff,vecdiffsigned,rmf2,rmftable,,o,p},
rtable=Table[func[t],{t,0,2Pi,inc}];
tantable=Table[tanfunc[func][t],{t,0,2Pi,inc}];
tablelength=Length@rtable;
scslengths=successiveLengths@rtable;
     linelength=lineLength@rtable;
     alpertable=With[{len=linelength},Table[N@scslengths[[n]]/len,{n,1,tablelength,1}]];
R1table=Table[R1func[func][n],{n,1,tablelength,1}];
R2table=Table[R2func[func][n],{n,1,tablelength,1}];
newnorm2[0]=normfunc[func][0];
Do[newnorm2[i]=R2table[[i]].R1table[[i]].newnorm2[i-1],{i,1,tablelength,1}];
Do[newline[n]=rtable[[n]]+newnorm2[n-1],{n,1,tablelength,1}];
Do[newvec[n]=vector2@{rtable[[n]],rtable[[n]]+newline[n]},{n,1,tablelength,1}];
(* check sign on vecdiff *)
vecdiff=VectorAngle[vector2@{rtable[[1]],newline[1]},vector2@{rtable[[tablelength]],newline[tablelength]}];
vecdiffsigned=If[RotationTransform[vecdiff,tantable[[tablelength]],rtable[[tablelength]]][newline[tablelength]]==newline[1],sign vecdiff,-sign vecdiff];
      Do[rmf2[n]=If[n==tablelength,rmf2[1],RotationTransform[alpertable[[n]]*vecdiffsigned,tantable[[n]],rtable[[n]]][newvec[n]]],{n,1,tablelength,1}];
     rmftable=Chop@N@Table[rmf2[n],{n,1,tablelength,1}];
{rmftable,tantable,rtable}
]


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



myalperfunc[func_]:=Hold[With[{linelength},Table[N@scslengths[[n]]/len,{n,1,tablelength,1}]];
alperfunc=Interpolation[Partition[Riffle[ttable,alpertable],2]]]


rotngontable[noside_,start_,init_,rad_][angle_]:=Module[{rtbl,rmf,tanv,alperdf,npts,one,ab,bb},
rtbl=With[{a=RotateLeft[Most@rtable,start]},Append[a,a[[1]]]];
rmf=With[{aa=RotateLeft[Most@rmftable,start]},Append[aa,aa[[1]]]];
tanv=With[{aaa=RotateLeft[Most@tanvectable,start]},Append[aaa,aaa[[1]]]];
alperdf=Prepend[RotateLeft[alperdiff,start],0];
npts=Table[rtbl[[tableno]]+rad*Normalize@vector2@{rtbl[[tableno]],rmf[[tableno]]},{tableno,1,tablelength,1}];
one=Table[Table[RotationTransform[t+init,tanv[[n]],rtbl[[n]]][npts[[n]]],{t,0,2Pi,2Pi/noside}],{n,1,tablelength,1}];
ab=Table[Append[RotationTransform[angle*Total@alperdf[[1;;n]],tanv[[n]],rtbl[[n]]][one[[n]]],rtbl[[n]]],{n,1,tablelength,1}];ab
]


(* ::Subsection:: *)
(*Puzzle Stuff*)


minmaxpointsposTest[pts_]:=Module[{a,alen,b,c,d,e,f,g,h,i},
a=minmaxpointspos@pts;
alen=Length@a;
b=pts[[#]]&/@a;
c=ed2@{b[[#]],RotateRight[b][[#]]}&/@Range[Length@b];
d=If[Length@a-20>=0,Length@a-20,2];
e=Reverse@Sort@Flatten[Position[c,Sort[c][[#]]]&/@Range[d]];
f[0]=a;
Do[f[n]=Drop[f[n-1],{e[[n]]}],{n,d,1,-1}];f[d]
]


mmptslongPts[points_]:=Module[{pts,mpts,mptspar,mptslong,mptslong2,knotpts,startendk,startend,psecl,psecr,pseclong,alfl,alfr,lineLl,lineLr,alftable,newptl,newptr},
pts=points;
mpts=minmaxpointsposTest@pts;
mptspar=Partition[mpts,5];
knotpts=Partition[pts[[#]]&@mpts,5];
startend=Table[{nn*101-100,nn*101},{nn,1,4,1}];
Do[mptslong[i]=Flatten@Join[{startend[[i]][[1]],mptspar[[i]],startend[[i]][[2]]}],{i,1,4,1}];
Do[psecl[1][i]=Reverse@pts[[mptslong[i][[1]];;mptslong[i][[2]]]],{i,1,4,1}];
Do[psecl[2][i]=pts[[mptslong[i][[2]];;mptslong[i][[3]]]],{i,1,4,1}];
Do[psecr[1][i]=pts[[mptslong[i][[6]];;mptslong[i][[7]]]],{i,1,4,1}];
Do[psecr[2][i]=Reverse@pts[[mptslong[i][[5]];;mptslong[i][[6]]]],{i,1,4,1}];
Do[lineLl[i]=lineLength@psecl[2][i],{i,1,4,1}];
Do[lineLr[i]=lineLength@psecr[2][i],{i,1,4,1}];
Do[alfl[1][i]=byArcLength@psecl[1][i],{i,1,4,1}];
Do[alfl[2][i]=byArcLength@psecl[2][i],{i,1,4,1}];
Do[alfr[1][i]=byArcLength@psecr[1][i],{i,1,4,1}];
Do[alfr[2][i]=byArcLength@psecr[2][i],{i,1,4,1}];
Do[newptl[i]=Nearest[pts,alfl[1][i][lineLl[i]]],{i,1,4,1}];
Do[newptr[i]=Nearest[pts,alfr[1][i][lineLr[i]]],{i,1,4,1}];
mptslong2=Table[Partition[Flatten@Join[{pts[[startend[[i]][[1]]]],newptl[i],knotpts[[i]],newptr[i],pts[[startend[[i]][[2]]]]}],3],{i,1,4,1}];
Flatten[mptslong2,1]
]


mmptslongptsPos[pts_]:=Partition[Union@Sort@Flatten@With[{list=mmptslongPts@pts},Position[pts,list[[#]]]&/@Range[Length@list]],9]


mmptslongPts2[points_]:=Quiet@Module[{pts,mpts,mptspar,mptslong,mptslong2,knotpts,startendk,startend,psecl,psecr,pseclong,alfl,alfr,lineLl,lineLr,alftable,newptl,newptr,mmpts,a,b,c,d,e,f,g,h,i,j,slope1pts,mmlist},
pts=points;
mpts=minmaxpointsposTest@pts;
mptspar=Partition[mpts,5];
knotpts=Partition[pts[[#]]&@mpts,5];
startend=Table[{nn*101-100,nn*101},{nn,1,4,1}];
Do[mptslong[i]=Flatten@Join[{startend[[i]][[1]],mptspar[[i]],startend[[i]][[2]]}],{i,1,4,1}];
Do[psecl[1][i]=Reverse@pts[[mptslong[i][[1]];;mptslong[i][[2]]]],{i,1,4,1}];
Do[psecl[2][i]=pts[[mptslong[i][[2]];;mptslong[i][[3]]]],{i,1,4,1}];
Do[psecr[1][i]=pts[[mptslong[i][[6]];;mptslong[i][[7]]]],{i,1,4,1}];
Do[psecr[2][i]=Reverse@pts[[mptslong[i][[5]];;mptslong[i][[6]]]],{i,1,4,1}];
Do[lineLl[i]=lineLength@psecl[2][i],{i,1,4,1}];
Do[lineLr[i]=lineLength@psecr[2][i],{i,1,4,1}];
Do[alfl[1][i]=byArcLength@psecl[1][i],{i,1,4,1}];
Do[alfl[2][i]=byArcLength@psecl[2][i],{i,1,4,1}];
Do[alfr[1][i]=byArcLength@psecr[1][i],{i,1,4,1}];
Do[alfr[2][i]=byArcLength@psecr[2][i],{i,1,4,1}];
Do[newptl[i]=Nearest[pts,alfl[1][i][lineLl[i]]],{i,1,4,1}];
Do[newptr[i]=Nearest[pts,alfr[1][i][lineLr[i]]],{i,1,4,1}];
mptslong2=Table[Partition[Flatten@Join[{pts[[startend[[i]][[1]]]],newptl[i],knotpts[[i]],newptr[i],pts[[startend[[i]][[2]]]]}],3],{i,1,4,1}];
mpts=Flatten[mptslong2,1];
mmlist=Partition[Union@Sort@Flatten@With[{list=mpts},Position[pts,list[[#]]]&/@Range[Length@list]],9];
a=Differences[Partition[pts,101][[#]][[All,1;;2]]]&/@Range[4];
b=Table[Abs@{Abs@#[[1]]-Abs@#[[2]]}&/@a[[n]],{n,1,4,1}];
c=Table[Sort@Flatten[((n-1)*101)+Position[b[[n]],#]&/@Sort[b[[n]]][[1;;12]]],{n,1,4,1}];
d=Map[Differences,c];
e=Flatten[Position[d[[#]],1]]&/@Range[4];
f=Complement[Range[12],e[[#]]]&/@Range[4];
g=IntegerPart[.5Differences[f[[#]]]]&/@Range[4];
h=With[{list1=Reverse@Rest@f[[#]],list2=Reverse@g[[#]]},Reverse@Table[list1[[n]]-list2[[n]],{n,1,Length@list1,1}]]&/@Range[4];
i=With[{list1=c[[#]][[h[[#]]]],list2=mmlist[[#]][[{4,6}]]},Flatten@Table[If[list1[[n]]>list2[[1]]\[And]list1[[n]]<list2[[2]],list1[[n]],{}],{n,1,Length@list1,1}]]&/@Range[4];
j=Flatten[{mmlist[[#]][[4]]+IntegerPart[.25Differences[mmlist[[#]][[{4,5}]]]],mmlist[[#]][[6]]-IntegerPart[.35Differences[mmlist[[#]][[{5,6}]]]]}]&/@Range[4];
slope1pts=Flatten@With[{len=Length@i[[#]]},Which[len==2,i[[#]],len==0,j[[#]],len==1,If[i[[#]][[1]]<mmlist[[#]][[5]],{i[[#]],j[[#]][[2]]},{j[[#]][[1]],i[[#]]}]]]&/@Range[4];Flatten[pts[[Sort[Flatten[Append[mmlist[[#]],slope1pts[[#]]]]]]]&/@Range[4],1]
]


mmptslongptsPos2[pts_]:=Partition[Union@Sort@Flatten@With[{list=mmptslongPts2@pts},Position[pts,list[[#]]]&/@Range[Length@list]],11]
