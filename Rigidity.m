(* ::Package:: *)

(* ::Section:: *)
(*Rigidity and stuff*)
(*Bryan Gin-ge Chen, August 2014*)


BeginPackage["Rigidity`"]

Begin["Global`"]


(* ::Section:: *)
(*Internal utilities*)


getatomindex[m_,n_,ind_,xx_,yy_,size_]:=(size yy(m-1)+size (n-1)+ind)

getatomindex2[cellcoords_,ind_,cover_,size_]:=Module[{dim=Length[cellcoords],increment=1,cover2=Join[cover,{size}]},
ind+
 Sum[increment=increment*cover2[[-i]];
increment*(cellcoords[[-i]]-1)
,{i,dim}]]

Doublemat[tab_]:=Module[{L=Length[tab]},Flatten[Table[{2tab[[j]]-1,2tab[[j]]},{j,L}]]]

(* Compute intersection "times" between two lines moving at unit speed, presented as point, angle *)
computeintersection[p1_,th1_,p3_,th3_]:=Module[{u1,u2,p2=p1+{Cos[th1],Sin[th1]},p4=p3+{Cos[th3],Sin[th3]},pos},
u1=((p4[[1]]-p3[[1]])(p1[[2]]-p3[[2]])-(p4[[2]]-p3[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
u2=((p2[[1]]-p1[[1]])(p1[[2]]-p3[[2]])-(p2[[2]]-p1[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
(*pos=p1+u1{Cos[th1],Sin[th1]};*)
{u1,u2(*,pos*)}
]


(* ::Section:: *)
(*Rigidity Matrix Functions*)


(* Fixed lattice matrix code *)
(* if fixedperiodic is false how do we deal with z's?? *)
(* convention for "lattice" columns agrees with papers *)

RigidityMatrix[z_,posns_,basis_,edgedat_,fixedperiodic_:False]:=Module[{numbonds=Length[edgedat],qdim=Length[z],dim=Length[posns[[1]]],numpart=Length[posns],part1,part2,ebond,kb,lattchange,zm,edatExtend},
SparseArray[Flatten[Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=1;(*edgedat[[j,3]];*)
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],Table[0,{qdim-Length[edgedat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
zm=Product[z[[k]]^edatExtend[[k]],{k,qdim}];
ebond=-posns[[part1]]+(posns[[part2]]+lattchange); (* sign convention from malestein theran *)
(* ebond=ebond/Norm[ebond];*)
If[part1!=part2,(Join[
Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],
Table[{j,dim (part2-1)+k}->ebond[[k]] zm,{k,dim}],
If[fixedperiodic,Flatten[Table[{j,dim numpart+(bvec-1) qdim+bcomponent}->edatExtend[[bvec]] (ebond[[bcomponent]]),{bvec,qdim},{bcomponent,dim}]],{}]
]),
(* part1\[Equal]part2*)
Join[Table[{j,dim (part1-1)+k}->-ebond[[k]](1-zm),{k,dim}],If[fixedperiodic,Flatten[Table[{j,dim numpart+(bvec-1) dim+bcomponent}->edatExtend[[bvec]](ebond[[bcomponent]]),{bvec,dim},{bcomponent,dim}]],{}]]
],
{j,numbonds}]]
,{numbonds,dim numpart+If[fixedperiodic,qdim*dim,0]}]
]

NRigidityMatrix[z_?(VectorQ[#,NumericQ]&),posns_,basis_,edgedat_,fixedperiodic_:False]:=RigidityMatrix[z,posns,basis,edgedat,fixedperiodic]


EdgeLengthsSq[posns_,basis_,edgedat_]:=Module[{part1,part2,kb,lattchange,qdim=Length[basis],ebond,numbonds=Length[edgedat],edatExtend},
Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=edgedat[[j,3]];
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],Table[0,{qdim-Length[edgedat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
ebond=-posns[[part1]]+(posns[[part2]]+lattchange); (* sign convention from malestein theran *)
Norm[ebond]^2
,
{j,numbonds}]]


NetDipole[posns_,basis_,edgedat_]:=Module[{vertcont,edgecont,dim=Length[posns[[1]]],qdim=Length[basis],nsp=NullSpace[basis],edatExtend},
vertcont=dim(Sum[posns[[j]],{j,Length[posns]}]);
edgecont=Sum[
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],Table[0,{qdim-Length[edgedat[[j,2]]]}]];
(posns[[edgedat[[j,1,1]]]]+posns[[edgedat[[j,1,2]]]]+edatExtend.basis)/2
,{j,Length[edgedat]}];
(Inverse[Transpose[Join[basis,nsp]]].(vertcont-edgecont))[[1;;qdim]]
]


KLWinding[z_,latticep_,basis_,latticeE_,cycle_,t_]:=Module[{powmat,w1,w2,zz},
powmat=RigidityMatrix[z,latticep,basis,latticeE];
zz=Det[powmat]/.cycle;
w1=NIntegrate[Im[D[Log[zz],t]],{t,0,2\[Pi]}];
-w1/(2\[Pi])
]


KLPolarization[latticep_,basis_,latticeEdat_,cyclesorigin_:{-1,-1}]:=Module[{powmat,w,zz,k,qdim=Length[basis],z,cycle,t},
powmat=RigidityMatrix[Table[z[j],{j,qdim}],latticep,basis,latticeEdat];
w=Table[
cycle=Table[z[k]->If[k!=j,cyclesorigin[[k]],Exp[I t]],{k,qdim}];
zz=Det[powmat]/.cycle;
NIntegrate[Im[D[Log[zz],t]],{t,0,2\[Pi]}]
,{j,qdim}];
-w/(2\[Pi])
]


(* ::Section:: *)
(*Constraints and Pebble related*)


ConstraintRows[numverts_,pinnedverts_,template_]:=Module[{dim=Length[template[[1]]]},
Table[Flatten[Table[If[k==pinnedverts[[j]],template[[j]],Table[0,{dim}]],{k,numverts}]],{j,Length[pinnedverts]}]]


PinnedRows[numverts_,verts_,dim_]:=Module[{unitvec},
Flatten[Table[
unitvec=Table[UnitVector[dim,k],{Length[verts]}];
ConstraintRows[numverts,verts,unitvec],
{k,dim}],1]]


(* create basis for zero modes localized on certain vertices *)
(* pebble basis generator;
peb is a list of ordered pairs of vertex indices {vertex that pebble is on, vertex that outgoing edge points to} *)
(*pebblebasismatrix[p_,E_,peb_]:=Module[{v=Length[p],e=Length[E],R=Normal[RigidityMatrix[{1,1},p,{{1,0},{0,1}},E]],pebloc,outvert,edgevec,perpvec},
If[MatrixRank[R]<e,Print["rows not independent"];,
If[Length[peb]!=2v-e,Print["wrong number of pebbles specified"];,Join[R,
Table[pebloc=peb[[j,1]];
outvert=peb[[j,2]];
edgevec=p[[pebloc]]-p[[outvert]];
perpvec={-edgevec[[2]],edgevec[[1]]};
Join[Table[0,{2pebloc-2}],perpvec,Table[0,{2v-2pebloc}]]
,{j,2v-e}]]]]
]*)

(* specify explicitly direction on each pebble ; peb here is a list, first component is location of pebble, second component is direction of mode *)
PebbleBasisModes[p_,E_,peb_,template_]:=Module[{v=Length[p],dim=Length[p[[1]]],e=Length[E],
R=Normal[RigidityMatrix[{},p,{},E]],pebloc,M,pebrows},
If[MatrixRank[R]<e,Print["edges not independent!"];,
If[Length[peb]!=dim v-e,Print["wrong number of pebbles specified"];,
pebrows=ConstraintRows[v,peb,template];
If[MatrixRank[pebrows]<Length[peb],Print["pebble constraints not independent!"];,
M=Join[R,pebrows];
Transpose[LinearSolve[M,ArrayFlatten[{{Table[0,{Length[peb]},{Length[peb]}]},{IdentityMatrix[Length[peb]]}}]]]]
]]
]

(* silly test with taking normal of constrained direction parallel rather than perpendicular to outgoing edge *)
(*pebblebasismatrixpar[p_,E_,peb_]:=Module[{v=Length[p],e=Length[E],R=Normal[RigidityMatrix[{1,1},p,{{1,0},{0,1}},E]],pebloc,outvert,edgevec,perpvec},
If[MatrixRank[R]<e,Print["rows not independent"];,
If[Length[peb]!=2v-e,Print["wrong number of pebbles specified"];,Join[R,
Table[pebloc=peb[[j,1]];
outvert=peb[[j,2]];
edgevec=p[[pebloc]]-p[[outvert]];
perpvec=edgevec;
Join[Table[0,{2pebloc-2}],perpvec,Table[0,{2v-2pebloc}]]
,{j,2v-e}]]]]
]*)


(* ::Section:: *)
(*Mode extraction / computation*)


(* give infinitesimal mode corresponding to CCW rotation about cent *)
infinitesimal2drotationmode[pos_,basis_:{},cent_:{0,0}]:=Module[{numparts=Length[pos],basisrot,posrot},
posrot=Table[{(pos[[j,2]]-cent[[2]]),-(pos[[j,1]]-cent[[1]])},{j,numparts}];
basisrot=Table[{basis[[j,2]],-basis[[j,1]]},{j,Length[basis]}];
Join[Flatten[posrot],If[Length[basis]>0,
Join[basisrot[[1]],
basisrot[[2]]]
,{}
]]
]

infinitesimalrotation[origin_,posns_]:=Module[{diff},
Flatten[Table[
diff=posns[[j]]-origin;
{-diff[[2]],diff[[1]]},{j,Length[posns]}]]]

getnontriv2D[pos_,basis_,edgedat_]:=Module[{pmtestk,testrotk,transx,transy,numatoms=Length[pos]},
pmtestk=Normal[RigidityMatrix[{1,1},pos,basis,edgedat,True]];
transx=Flatten[Join[Table[{1,0},{numatoms}],Table[0,{4}]]];
transy=Flatten[Join[Table[{0,1},{numatoms}],Table[0,{4}]]];;
testrotk=infinitesimal2drotationmode[pos,basis];
NullSpace[Join[pmtestk,{transx,transy,testrotk}]][[1]]]


(* need this to be cromulent with CoveringFrameworkVerts and CoveringFrameworkEdges *)
CoveringMotion[mode_,cover_,periodic_:False]:=Module[{dim=Length[cover],numparts,tabspec,m,ind},
(* dim*number of particles + dim^2 = length of mode vector*)
If[Mod[Length[mode],dim]!=0,Print["bad mode length"];Abort[]];
numparts=(Length[mode]-dim^2)/dim; (* y then x *)
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Join[Flatten[
Table[
Table[
Sum[ind=dim numparts+dim (j-1);
mode[[ind+1;;ind+dim]]*m[j],{j,dim}]
+mode[[dim (i-1)+1;;dim (i-1)+dim]],
{i,numparts}],
##]&@@tabspec (* specification of table, dim copies of loops from 0 to cover-1 *)
],
If[periodic,
Flatten[Table[
ind=dim numparts+dim(j-1);
cover[[j]]mode[[ind+1;;ind+dim]],{j,dim}]],{}]
]
]


(* this should yield the elastic displacements in a spring network *)
HarmonicExtension[Lap_,bvtr_,u_]:=Module[{l=Dimensions[Lap][[1]]/2,inter,dinter,cinter,matB,matC,fI,ans},
(* need to be careful with "Complement" because does not preserve ordering *)
inter=Complement[Table[j,{j,l}],bvtr];
dinter=Doublemat[inter];
cinter=Doublemat[bvtr];
matB=Lap[[dinter,cinter]];
matC=Lap[[dinter,dinter]];
If[Det[matC]==0,
Print["Rank deficient; system is floppy"];,
fI=-Inverse[matC].matB.u; (* Schur complement *)
ans=Table[0,{2l}];
Do[ans[[dinter[[j]]]]=fI[[j]];,{j,Length[fI]}];
Do[ans[[cinter[[j]]]]=u[[j]];,{j,Length[u]}];
ans]
]

(* Dirichlet to Neumann operator *)
DtN[Lap_,bvtr_]:=Module[{l=Dimensions[Lap][[1]]/2,inter,dinter,cinter,matA,matB,matC,matD},
inter=Complement[Table[j,{j,l}],bvtr];
dinter=Doublemat[inter];
cinter=Doublemat[bvtr];
matA=Lap[[cinter,cinter]];
matB=Lap[[cinter,dinter]];
matC=Lap[[dinter,cinter]];
matD=Lap[[dinter,dinter]];
matA-matB.Inverse[matD].matC (* Schur complement *)
]


(*pos slope, zero slope, neg slope line-localized modes for untwisted kagome*)
poslinemode[i_,m_,n_]:=Module[{d=Table[0,{6m n}],loc},
Do[loc=3n(i-1)+3(j-1)+2;
d[[2loc-1]]=3/4;
d[[2loc]]=Sqrt[3]/4;
d[[2loc+1]]=0;
d[[2loc+2]]=Sqrt[3]/2;,{j,n}];d]
zerolinemode[i_,m_,n_]:=Module[{d=Table[0,{6m n}],loc},
Do[loc=3(i-1)+3n(j-1)+1;
d[[2loc-1]]=-(3/4);
d[[2loc]]=-(Sqrt[3]/4);
d[[2loc+3]]=-(3/4);
d[[2loc+4]]=Sqrt[3]/4;,{j,m}];d]
neglinemode[i_,m_,n_]:=Module[{d=Table[0,{6m n}],loc},
Do[loc=If[i<m+n-i,3(i-1)+3(n-1)(j-1)+1,3m n-3(m+n-i)-3(n-1)(j-1)+1];
d[[2loc-1]]=0;
d[[2loc]]=-(Sqrt[3]/2);
d[[2loc+1]]=3/4;
d[[2loc+2]]=-(Sqrt[3]/4);,{j,Min[m+n-i,i]}];d]


(* ::Section:: *)
(*Some basic 2 D lattices*)


(* ::Subsection:: *)
(*vertex positions*)


(*square lattice*)
SqLattice[xx_,yy_,r_:0]:=(* yy better be even? *) Flatten[Table[{m,n}+RandomReal[{-r,r},2],{m,0,xx-1},{n,0,yy-1}],1];

SqLatticeSlopes[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{slopesx=RandomReal[{-r,r},xx],slopesy=RandomReal[{-r,r},yy],time},
Flatten[Table[
time=computeintersection[{m,0},\[Pi]/2+slopesx[[m+1]],{0,n},slopesy[[n+1]]];
{0,n}+time [[2]]{Cos[slopesy[[n+1]]],Sin[slopesy[[n+1]]]}
,{m,0,xx-1},{n,0,yy-1}],1]];

(* kagome in the form of a rhombus *)
KagLatticeRho[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Flatten[Table[Table[{(*Mod[m+1/2.n,xx]*)m+1/2 n,Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}+RandomReal[{-r,r},2]+1/(2 Sqrt[3]Cos[th]) {Cos[\[Pi]/6+2 \[Pi]/3 i+th],Sin[\[Pi]/6+2 \[Pi]/3 i+th]},{i,3}],{m,1,xx},{n,0,yy-1}],2];

(* kagome in the form of a rectangle *)
KagLatticeRec[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Flatten[Table[Table[{m+1/2 Mod[n,2],Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}+If[r>0,RandomReal[{-r,r},2],0]+1/(2 Sqrt[3]Cos[th]) {Cos[\[Pi]/6+2 \[Pi]/3 i+th],Sin[\[Pi]/6+2 \[Pi]/3 i+th]},{i,3}],{m,1,xx},{n,0,yy-1}],2];

(* triangular lattice in the form of rhombus *)
TriLatticeRho[xx_,yy_,r_:0]:=(* yy better be even? *) Flatten[Table[{(*Mod[m+1/2.n,xx]*)m+1/2. n,Sqrt[3]/2. n}+RandomReal[{-r,r},2],{m,1,xx},{n,0,yy-1}],1];

(*triangular lattice in the form of rectangle *)
TriLatticeRec[xx_,yy_,r_:0]:=(* yy better be even? *) Flatten[Table[{Mod[m+1/2. n,xx],Sqrt[3]/2. n}+RandomReal[{-r,r},2],{m,1,xx},{n,0,yy-1}],1];

(* honeycomb in the form of a rectangle *)
HoneycombLattice[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{temp},temp=Flatten[Table[Table[If[((Mod[m+1/2 n,xx]==0)&&(i==1))||((Mod[m+1/2 n,xx]==xx-1/2)&&(i==2)),{},{Mod[m+1/2 n,xx],Sqrt[3]/2 n}+If[r>0,RandomReal[{-r,r},2],0]+(-1)^i /(2Sqrt[3]){Sqrt[3]/2,1/2}],{i,2}],{m,1,xx},{n,0,yy-1}],2];
Replace[temp,x_List:>DeleteCases[x,{}],{0,Infinity}]
]

makekaglatticerunit[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Flatten[Table[{(*Mod[m+1/2.n,xx]*)m+1/2 n,Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}+RandomReal[{-r,r},2],{m,1,xx},{n,0,yy-1}],1];

makekaglatticeunit[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Flatten[Table[{Mod[m+1/2 n,xx],Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}+RandomReal[{-r,r},2],{m,1,xx},{n,0,yy-1}],1];


(* ::Subsection:: *)
(*edge stuff*)


(* return a list of pairs of vertices corresponding to edges, first list is NN, second list is NNN *)
SqLatticeEdges[xx_,yy_]:=(* yy better be even? *) Module[{index=0,bondlist=Table[Null,{2xx*yy-xx-yy}],numbonds=0,nextbondlist=Table[Null,{(xx-1)*(yy-1)}],numnextbonds=0,nextbondlistother=Table[Null,{(xx-1)*(yy-1)}]},
Do[
index++;
If[n>1,
numbonds++;
bondlist[[numbonds]]={{index,index-1},{},1};
];
If[m>1,
numbonds++;
bondlist[[numbonds]]={{index,index-yy},{},1};
];
If[(m>1)&&(n>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-yy-1},{},1};
nextbondlistother[[numnextbonds]]={{index-1,index-yy},{},1};
];
,{m,xx},{n,yy}];
bondlist=bondlist[[1;;numbonds]];
nextbondlist=nextbondlist[[1;;numnextbonds]];
{bondlist,nextbondlist,nextbondlistother}
];

(* for rectangle only; finally fixed *)
KagLatticeRecEdges[xx_,yy_]:=Module[{index=0,bondlist=Table[Null,{6xx*yy}],numbonds=0,nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],numnextbonds=0},
Do[ (* loop over i from 1 to 3 *)
index++; (* particle number *)
If[i==2,
numbonds++; (* bond number *)
bondlist[[numbonds]]={{index,index-1},{},1};
If[(n>1),
If[Mod[n,2]==0,
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-4},{},1};
];
numbonds++;
bondlist[[numbonds]]=If[Mod[n,2]==1,{{index,index-4},{},1},{{index,index-2},{},1}];
If[(Mod[n,2]==0)&&(m<xx),
numbonds++;
bondlist[[numbonds]]={{index,index+3*yy-4},{},1};
];
If[(Mod[n,2]==1)&&(m>1),
numbonds++;
bondlist[[numbonds]]={{index,index-3*yy-2},{},1};
];
];
If[(m>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-3*yy+1},{},1};
If[(Mod[n,2]==1)&&(n>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-3*yy-4},{},1};
];
];
];
If[i==3,
numbonds++;
bondlist[[numbonds]]={{index,index-1},{},1};
numbonds++;
bondlist[[numbonds]]={{index,index-2},{},1};
];
If[(i==1)&&(m>1),
numbonds++;
bondlist[[numbonds]]={{index,index-3*yy+2},{},1};
If[(n<yy)&&(Mod[n,2]==1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-3*yy+5},{},1};
];
];
If[(i==1)&&(Mod[n,2]==0)&&(n<yy),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index+5},{},1};
];
,{m,xx},{n,yy},{i,3}];
bondlist=bondlist[[1;;numbonds]];
nextbondlist=nextbondlist[[1;;numnextbonds]];
{bondlist,nextbondlist}
];

(* for rhombus only *)
KagLatticeRhoEdges[xx_,yy_]:=Module[{index=0,bondlist=Table[Null,{6xx*yy}],numbonds=0,nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],numnextbonds=0},
Do[
index++;
If[i==2,
numbonds++;
bondlist[[numbonds]]={{index,index-1},{},1};
If[(n>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-4},{},1};
numbonds++;
bondlist[[numbonds]]={{index,index-2},{},1};
];
If[(m>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-3*yy+1},{},1};
];
];
If[i==3,
numbonds++;
bondlist[[numbonds]]={{index,index-1},{},1};
numbonds++;
bondlist[[numbonds]]={{index,index-2},{},1};
];
If[(i==1)&&(m>1),
numbonds++;
bondlist[[numbonds]]={{index,index-3*yy+2},{},1};
If[(n<yy),
numbonds++;
bondlist[[numbonds]]={{index,index-3*yy+4},{},1};
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-3*yy+5},{},1};
];
];
,{m,xx},{n,yy},{i,3}];
bondlist=bondlist[[1;;numbonds]];
nextbondlist=nextbondlist[[1;;numnextbonds]];
{bondlist,nextbondlist}
];

(*
periodic version !  ! make periodic in horizontal direction first
 return a list of pairs of vertices corresponding to edges, first list is NN, second list is NNN *)
(*this function generates two lists of edges relevant for a square lattice with periodic boundary conditions in the x-direction,the first is nearest neighbors,and the second is next nearest neighbors*)
SqLatticexperEdges[xx_,yy_]:=(* yy better be even? *) Module[{index=0,bondlist=Table[Null,{2xx*yy-xx}],numbonds=0,nextbondlist=Table[Null,{(xx)*(yy-1)}],numnextbonds=0,nextbondlistother=Table[Null,{(xx)*(yy-1)}]},
Do[
index++;
If[n>1,
numbonds++;
(* vertical bonds *)
bondlist[[numbonds]]={{index,index-1},{0,0},1};
];
If[m==1,
numbonds++;
(* periodic horizontal bonds*)
bondlist[[numbonds]]={{index,index+(xx-1)yy},{-1,0},1};
];
If[m>1,
numbonds++;
(* horizontal bonds *)
bondlist[[numbonds]]={{index,index-yy},{0,0},1};
];
If[(m==1)&&(n>1),
numnextbonds++;
(* periodic diagonal bonds *)
nextbondlist[[numnextbonds]]={{index,index+(xx-1)yy-1},{-1,0},1};
nextbondlistother[[numnextbonds]]={{index-1,index+(xx-1)yy},{-1,0},1}
];
If[(m>1)&&(n>1),
numnextbonds++;
(* diagonal bonds *)
nextbondlist[[numnextbonds]]={{index,index-yy-1},{0,0},1};
nextbondlistother[[numnextbonds]]={{index-1,index-yy},{0,0},1}
];
,{m,xx},{n,yy}];
bondlist=bondlist[[1;;numbonds]];
nextbondlist=nextbondlist[[1;;numnextbonds]];
{bondlist,nextbondlist,nextbondlistother}
];

KagLatticexperEdges[xx_,yy_]:=(* 1,2,3, go around counter clockwise from 5\[Pi]/6*)Module[{index=0,bondlist=Table[Null,{6xx*yy+2yy-1}],numbonds=0,nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],nextbondlist2=Table[Null,{3*(xx)*(yy)+xx+yy-2}],numnextbonds=0,numnextbonds2=0},
Do[
index++;
If[i==2,
numbonds++;
bondlist[[numbonds]]={{index,index-1},{0,0},1}; (* triangle bond, 1 to 2 \ *)
If[(n>1),
numnextbonds++;
nextbondlist[[numnextbonds]]={{index,index-4},{0,0},1}; (* next nearest neighbor bond, 2 to 1 / *)
numbonds++;
bondlist[[numbonds]]={{index,index-2},{0,0},1}; (* inter triangle bond, 2 to 3 / *)
];
If[(m>1), (* next nearest neighbor bonds *)
numnextbonds++; (* connect to previous column, 2 to 3 \ *)
nextbondlist[[numnextbonds]]={{index,index-3*yy+1},{0,0},1};,
(* m\[Equal]1 case *)
numnextbonds++;
 (* connect to previous column, 2 to 3 \ *)
nextbondlist[[numnextbonds]]={{index,index+3*yy*(xx-1)+1},{-1,0},1};
];
];
If[i==3, (* triangle bonds 2 to 3 / and 1 to 3 - *)
numbonds++;
bondlist[[numbonds]]={{index,index-1},{0,0},1};
numbonds++;
bondlist[[numbonds]]={{index,index-2},{0,0},1};
If[(n<yy),
numnextbonds2++; (* next nearest bond 3 to 1 | *) 
nextbondlist2[[numnextbonds2]]={{index,index+1},{0,0},1};
If[(m>1),
numnextbonds2++; (*  next nearest bond 3 to 2 \ *)
nextbondlist2[[numnextbonds2]]={{index,index-3 yy+2},{0,0},1};
,
numnextbonds2++; (*  next nearest bond 3 to 2 \ *)
nextbondlist2[[numnextbonds2]]={{index,index+3 yy(xx-1)+2},{-1,0},1};
]
];
];
If[(i==1)&&(m>1),
numbonds++;(* inter triangle bond 1 to 3  - *)
bondlist[[numbonds]]={{index,index-3*yy+2},{0,0},1};
If[(n<yy),
numbonds++; (* inter triangle bond \ 1 to 2 *)
bondlist[[numbonds]]={{index,index-3*yy+4},{0,0},1};
numnextbonds++; (* next nearest bond 1 to 3 vertical bond | *)
nextbondlist[[numnextbonds]]={{index,index-3*yy+5},{0,0},1};
];
If[(n>1),
numnextbonds2++; (*  next nearest bond 1 to 2 / *)
nextbondlist2[[numnextbonds2]]={{index,index-3 yy+1},{0,0},1};
]
];
If[(i==1)&&(m==1),
numbonds++;(* inter triangle bond 1 to 3  - *)
bondlist[[numbonds]]={{index,index+3*yy*(xx-1)+2},{-1,0},1};
If[(n<yy),
numbonds++;(* inter triangle bond \ 1 to 2 *)
bondlist[[numbonds]]={{index,index+3*yy*(xx-1)+4},{-1,0},1};
numnextbonds++;(* next nearest bond 1 to 3 vertical bond | *)
nextbondlist[[numnextbonds]]={{index,index+3*yy*(xx-1)+5},{-1,0},1};
];
If[(n>1),
numnextbonds2++; (*  next nearest bond 1 to 2 / *)
nextbondlist2[[numnextbonds2]]={{index,index+3 yy(xx-1)+1},{-1,0},1};
]
];
,{m,xx},{n,yy},{i,3}];
bondlist=bondlist[[1;;numbonds]];
nextbondlist=nextbondlist[[1;;numnextbonds]];
nextbondlist2=nextbondlist2[[1;;numnextbonds2]];
{bondlist,nextbondlist,nextbondlist2}
];


(* ::Subsection:: *)
(*getting boundary vertices*)


(* returns list of ordered pairs of vertex indices {vertex that pebble is on, vertex that outgoing edge points to} *)
boundaryvertskagr[m_,n_]:=Module[{horiz={},minusbot={},minusright={},plus},
horiz=Table[{3(j-1)+1,3(j-1)+2},{j,n}];
minusbot=Table[{3(j-1)n+2,3(j-1)n+3},{j,m}];
minusright=Table[{3(m-1) n+3(j-1)+2,3(m-1) n+3(j-1)+3},{j,2,n}];
plus=Table[{3n  j-3+3,3n  j-3+1},{j,m}];
Join[horiz,minusbot,minusright,plus]]

(* just a list of vertex indices *)
boundaryvertstrir[m_,n_]:=Module[{left={},bot={},top={},right={}},
left=Table[j,{j,n}];
bot=Table[n j+1,{j,m-1}];
top=Table[n j,{j,2,m}];
right=Table[n (m-1)+j,{j,2,n-1}];
Join[left,bot,top,right]]

splitbctrir[m_,n_,l_,b_,t_,r_]:=Module[{left={},bot={},top={},right={}},
left=Table[l,{j,n}];
bot=Table[b,{j,m-1}];
top=Table[t,{j,2,m}];
right=Table[r,{j,2,n-1}];
Flatten[{left,bot,top,right}]]


boundaryverts2by2sq[xx_,yy_]:=Module[{ind,indout},Join[
(*left edge pebbles *)
ind=1;
indout=2;
Table[{getatomindex[1,n,ind,xx,yy,4],getatomindex[1,n,indout,xx,yy,4]},{n,yy}],
(*top edge pebbles *)
ind=2;
indout=4;
Table[{getatomindex[m,yy,ind,xx,yy,4],getatomindex[m,yy,indout,xx,yy,4]},{m,xx}],
(*bottom edge pebbles *)
ind=3;
indout=1;
Table[{getatomindex[m,1,ind,xx,yy,4],getatomindex[m,1,indout,xx,yy,4]},{m,xx}],
(*right edge pebbles *)
ind=4;
indout=3;
Table[{getatomindex[xx,n,ind,xx,yy,4],getatomindex[xx,n,indout,xx,yy,4]},{n,yy}]]]

boundaryvertssq[xx_,yy_]:=Module[{ind,indout},Join[
(*left edge pebbles *)
ind=1;
indout=3;
Table[{getatomindex[1,n,ind,xx,yy,4],getatomindex[1,n,indout,xx,yy,4]},{n,yy}],
(*left edge pebbles *)
ind=2;
indout=4;
Table[{getatomindex[1,n,ind,xx,yy,4],getatomindex[1,n,indout,xx,yy,4]},{n,yy}],
(*top edge pebbles *)
ind=2;
indout=1;
Table[{getatomindex[m,yy,ind,xx,yy,4],getatomindex[m,yy,indout,xx,yy,4]},{m,xx}],
(*top edge pebbles *)
ind=4;
indout=3;
Table[{getatomindex[m,yy,ind,xx,yy,4],getatomindex[m,yy,indout,xx,yy,4]},{m,xx}]]]


(* create lists suitable for input into the last two slots of HarmonicExtension; the first being the indices of the "boundary" vertices and the second being the actual applied forces / displacements there  *)
shearbvsq[lx_,ly_,u_:{1,0}]:={(* site indices *) Join[Table[ly(j-1)+1,{j,lx}],Table[ly j,{j,lx}]], 
(* applied displacement components; 0 on bottom, u on top *) Join[Table[0,{2lx}],Flatten[Table[u,{lx}]]]}


BoundaryVerts[edgedat_,cover_,cellspec_]:=Module[{qdim=Length[cover],tabspec,m,list,unitcellsize=Max[edgedat[[All,1]]](*,parts*)},
(*parts=Table[0,{2qdim}];*)
list=Table[
{tabspec=Table[If[i!=k,{m[i],cover[[i]]},
{m[k],1}],{i,qdim}];
Flatten[Table[
(*parts[[2k-1]]+=Length[cellspec[[k,1]]];*)
getatomindex2[Table[m[j],{j,qdim}],cellspec[[k,1]],cover,unitcellsize]
,##]&@@tabspec],
tabspec=Table[If[i!=k,{m[i],cover[[i]]},
{m[k],cover[[k]],cover[[k]]}],{i,qdim}];
Flatten[Table[
(*parts[[2k]]+=Length[cellspec[[k,2]]];*)
getatomindex2[Table[m[j],{j,qdim}],cellspec[[k,2]],cover,unitcellsize]
,##]&@@tabspec]
}
,{k,qdim}](*{list,parts}*)
]


(* ::Section:: *)
(*Making new lattices from scratch and from old*)


(*Function to make edges for points in "lattice" closer than "dis" *)
DiskGraphEdges[pos_,dis_,basis_:{},maxwinding_:1]:=Module[{numverts=Length[pos],qdim=Length[basis],tabspec,m,cover},
If[Length[basis]==0,
Reap[Do[If[i!=j,
If[Norm[pos[[i]]-pos[[j]]]<=dis,
Sow[{{i,j},{},1}]]
],{i,numverts},{j,i,numverts}]][[2,1]],
cover=If[Depth[maxwinding]==1,Table[maxwinding,{qdim}],maxwinding];
tabspec=Table[{m[i],-cover[[i]],cover[[i]]},{i,qdim}];
Reap[Do[If[i!=j,
Do[
If[Norm[pos[[i]]-pos[[j]]-Sum[basis[[k]]*m[k],{k,qdim}]]<=dis,
Sow[{{i,j},Table[m[k],{k,qdim}],1}]],
##]&@@tabspec
],{i,numverts},{j,i,numverts}]][[2,1]]
]
]


(* make a list of vertex positions in any dimension *)
CoveringFrameworkVerts[unitcell_,latt_,cover_,r_:0]:=Module[{qdim=Length[latt],dim=Length[unitcell[[1]]],tabspec,m},
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Flatten[
Table[
Table[
Sum[latt[[i]]*m[i],{i,qdim}]+RandomReal[{-r,r},dim]+unitcell[[i]],
{i,Length[unitcell]}],
##]&@@tabspec,(* specification of table, dim copies of loops from 0 to cover-1 *)
qdim]
];


(* this function was broken!!! *)
CoveringFrameworkEdges[edgedat_,cover_,periodic_:False]:=Module[{dim=Length[cover],ind1,ind2,p1,p2,a,m,numbonds=0,bondlist=Table[Null,{Length[edgedat](Times@@cover)}],lenedge=Length[edgedat],unitcellsize=Max[edgedat[[All,1]]],cellchange,tabspec,i},
tabspec=Join[Table[{m[j],cover[[j]]},{j,dim}],{{i,lenedge}}];
Do[(* loop over edges in edgedat, (i.e. copy an edge i into all cells m,n) *)
{p1,p2}=edgedat[[i,1]];
(*a=edgedat[[i,2]];*)
a=Join[edgedat[[i,2,1;;Min[Length[edgedat[[i,2]]],dim]]],Table[0,{dim-Length[edgedat[[i,2]]]}]];
ind1=getatomindex2[Table[m[j],{j,dim}],p1,cover,unitcellsize];
ind2=getatomindex2[Table[Mod[m[j]+a[[j]],cover[[j]],1],{j,dim}],p2,cover,unitcellsize];
cellchange=Table[
(* ceiling -1 because we need right endpoint *)
Ceiling[(m[j]+a[[j]])/cover[[j]]-1],{j,dim}];
If[periodic||(cellchange==Table[0,{dim}]),
numbonds++;
bondlist[[numbonds]]={{ind1,ind2},cellchange,1}
];
,##]&@@tabspec;
bondlist[[1;;numbonds]]
]

(* slice; remove vertices, edges under a certain condition *)
(* return new edgedat and list of vertex indices *)
SliceOffVerts[pos_,edgedat_,poscond_,indexcond_:False]:=Module[{edgenew,keepers,numpartsold=Length[pos],throwers},
keepers=Flatten[Position[pos,_?(poscond),{1},Heads->False]];
keepers=Select[keepers,Not[indexcond]];
throwers=Complement[Table[i,{i,numpartsold}],keepers];
edgenew=Select[edgedat,Flatten[Intersection[#[[1]],throwers]]=={}&]; (* need to reindex ... *)
edgenew=Table[{edgenew[[j,1]]/.Table[keepers[[j]]->j,{j,Length[keepers]}],edgenew[[j,2]],edgenew[[j,3]]},{j,Length[edgenew]}];
{edgenew,keepers}]


glueedges[botE_,topE_,botdims_,botsize_,topdims_,topsize_,face_,cellglue_]:=Module[{dim=Length[topdims],connectors,tabspec,ind,indbot,indtop,m,k},
tabspec=Table[
If[j<face,ind=j,ind=j+1];
{m[j],botdims[[ind]]},{j,dim-1}];
tabspec=Join[tabspec,{{k,botsize}}];
(* find pairs of corresponding vertices in bot and top *)
connectors = Flatten[Table[
ind=Insert[Table[m[l],{l,dim-1}],botdims[[face]],face];
indbot=getatomindex2[ind,k,botdims,botsize];
ind=Insert[Table[m[l],{l,dim-1}],1,face];
Table[
indtop=getatomindex2[ind,cellglue[[k,l]],topdims,topsize];
{indbot,indtop+Max[botE]}
,{l,Length[cellglue[[k]]]}]
,##]&@@tabspec,dim];
(* glue along dimension"face"*)
Join[botE,topE+Max[botE],connectors]
]

glueverts[botV_,topV_,vec_]:=Join[botV,topV+Table[vec,{Length[topV]}]]


(* ::Section:: *)
(*Graphics functions*)


Draw2DFramework[p_,E_,pointstyle_:{},linestyle_:{}]:=Module[{e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]]
}]]


Draw2DFrameworkStress[p_,E_,stress_,mthick_:.01,colors_:{Purple,Orange}]:=Module[{e=Length[E],nstr=mthick stress/Max[Abs[stress]]},
Graphics[{Table[{If[nstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[nstr[[j]]]],Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}]},{j,e}]}]]


Draw2DFrameworkMode[p_,E_,nv_,pointstyle_:{},linestyle_:{},col_:{Red}]:=Module[{e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[Line[{p[[i]],p[[i]]+nv[[2i-1;;2i]]}],{i,Length[p]}]]
}]]


DrawPeriodic2DFramework[p_,basis_,E_,copies_:{},pointstyle_:{},linestyle_:{}]:=Module[{e=Length[E],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]+cellshift]},{i,Length[p]}]]}
,##]&@@tabspec
]
]


DrawPeriodic2DFrameworkStress[p_,basis_,E_,stress_,copies_:{},mthick_:.01,colors_:{Purple,Orange}]:=Module[{e=Length[E],nstr=mthick stress/Max[Abs[stress]],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
{If[nstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[nstr[[j]]]],Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}]},{j,e}]
,##]&@@tabspec
]]


DrawPeriodic2DFrameworkMode[p_,basis_,E_,nv_,copies_:{},pointstyle_:{},linestyle_:{},col_:Red]:=Module[{e=Length[E],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]+cellshift]},{i,Length[p]}]],
Join[col,Table[Line[{p[[i]]+cellshift,p[[i]]+cellshift+nv[[2i-1;;2i]]}],{i,Length[p]}]]
}
,##]&@@tabspec
]
]


Draw3DFramework[p_,E_,pointstyle_:{},linestyle_:{}]:=Module[{e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]]
}]]


Draw3DFrameworkStress[p_,E_,stress_,mthick_:.01,colors_:{Purple,Orange}]:=Module[{e=Length[E],nstr=mthick stress/Max[Abs[stress]]},
Graphics3D[{
Table[{
If[nstr[[j]]>0,colors[[1]],colors[[2]]],
AbsoluteThickness[Abs[nstr[[j]]]],
Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}]},{j,e}]
}]]


Draw3DFrameworkMode[p_,E_,nv_,pointstyle_:{},linestyle_:{},col_:{Red}]:=Module[{e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[Line[{p[[i]],p[[i]]+nv[[3i-2;;3i]]}],{i,Length[p]}]]
}]]


DrawPeriodic3DFramework[p_,basis_,E_,copies_:{},pointstyle_:{},linestyle_:{}]:=Module[{e=Length[E],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]+cellshift]},{i,Length[p]}]]}
,##]&@@tabspec
]
]


DrawPeriodic3DFrameworkStress[p_,basis_,E_,stress_,copies_:{},mthick_:.01,colors_:{Purple,Orange}]:=Module[{e=Length[E],nstr=mthick stress/Max[Abs[stress]],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
{If[nstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[nstr[[j]]]],Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}]},{j,e}]
,##]&@@tabspec
]]


DrawPeriodic3DFrameworkMode[p_,basis_,E_,nv_,copies_:{},pointstyle_:{},linestyle_:{},col_:{Red}]:=Module[{e=Length[E],dim=Length[basis],tabspec,m,cover,cellshift,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
cellshift=Sum[m[i]*basis[[i]],{i,dim}];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{p[[E[[j,1,1]]]]+cellshift,p[[E[[j,1,2]]]]+edatExtend.basis+cellshift}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]+cellshift]},{i,Length[p]}]],
Join[col,Table[Line[{p[[i]]+cellshift,p[[i]]+cellshift+nv[[3i-2;;3i]]}],{i,Length[p]}]]
}
,##]&@@tabspec
]
]


reciprocbasis[qx_,qy_,basis_]:={qx,qy}.Inverse[basis];

BandPlot[{zx_,zy_},poly_,basis_:{{1,0},{0,1}},xwind_:{-\[Pi],\[Pi]},ywind_:{-\[Pi],\[Pi]},opts_:{MaxRecursion->Automatic}]:=Module[{qx,qy,b,rec},
ContourPlot[(* this seems to work, but I should rederive it to make sure... *)
(* checked with Jayson, we had to reverse qx, qy because vectors get relabeled after 90 degree rotation *)
Evaluate[rec=reciprocbasis[qy,qx,LeviCivitaTensor[2].basis];(poly/.{zx->Exp[I rec[[1]]],zy->Exp[I rec[[2]]]})],
{qx,xwind[[1]],xwind[[2]]},{qy,ywind[[1]],ywind[[2]]},opts]]


(* ::Section:: *)
(*End*)


End[];
EndPackage[]
