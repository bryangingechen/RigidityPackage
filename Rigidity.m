(* ::Package:: *)

(* ::Section:: *)
(*Rigidity and stuff*)
(*Bryan Gin-ge Chen, August 2014*)


BeginPackage["Rigidity`"]

Begin["Global`"]


(* ::Section:: *)
(*Internal utilities*)


getatomindex[m_,n_,ind_,xx_,yy_,size_]:=(size yy(m-1)+size (n-1)+ind)

getatomindex2[cellcoords_,ind_,cover_,size_]:=
Module[{i,dim=Length[cellcoords],increment=1,cover2=Join[cover,{size}]},
ind+
 Sum[increment=increment*cover2[[-i]];
increment*(cellcoords[[-i]]-1)
,{i,dim}]];

Doublemat[tab_]:=Module[{L=Length[tab],j},Flatten[Table[{2tab[[j]]-1,2tab[[j]]},{j,L}]]];

PosVecIndices[tab_,d_]:=Module[{L=Length[tab],j,k},Flatten[Table[Table[d tab[[j]]-d+k,{k,d}],{j,L}]]];

(* Compute intersection "times" between two lines moving at unit speed, presented as point, angle *)
computeintersection[p1_,th1_,p3_,th3_]:=
Module[{u1,u2,p2=p1+{Cos[th1],Sin[th1]},p4=p3+{Cos[th3],Sin[th3]}},
u1=((p4[[1]]-p3[[1]])(p1[[2]]-p3[[2]])-(p4[[2]]-p3[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
u2=((p2[[1]]-p1[[1]])(p1[[2]]-p3[[2]])-(p2[[2]]-p1[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
(*pos=p1+u1{Cos[th1],Sin[th1]};*)
{u1,u2(*,pos*)}
];

(* Compute intersection point between two lines moving at unit speed, presented as point, angle *)
computeintersectionpos[p1_,th1_,p3_,th3_]:=
Module[{u1,u2,p2=p1+{Cos[th1],Sin[th1]},p4=p3+{Cos[th3],Sin[th3]},pos},
u1=((p4[[1]]-p3[[1]])(p1[[2]]-p3[[2]])-(p4[[2]]-p3[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
u2=((p2[[1]]-p1[[1]])(p1[[2]]-p3[[2]])-(p2[[2]]-p1[[2]])(p1[[1]]-p3[[1]]))/((p4[[2]]-p3[[2]])(p2[[1]]-p1[[1]])-(p4[[1]]-p3[[1]])(p2[[2]]-p1[[2]]));
pos=p1+u1{Cos[th1],Sin[th1]};
pos
];


(* Smith Normal Form code from Daniel Lichtblau
http://mathematica.stackexchange.com/a/40930
 *)
diagonalQ[mat_?MatrixQ]:=With[{posns=Flatten[Map[Position[#,_?(#!=0&)]&,mat]]},
Length[Union[posns]]==Length[posns]]

diagonalize[mat_?MatrixQ]:=Module[{hnf=mat,umat=IdentityMatrix[Length[mat]],
vmat=IdentityMatrix[Length[mat[[1]]]],tmpu,tmpv},
While[Not[diagonalQ[hnf]],{tmpu,hnf}=HermiteDecomposition[hnf];
umat=tmpu.umat;
{tmpv,hnf}=HermiteDecomposition[Transpose[hnf]];
vmat=vmat.Transpose[tmpv];
hnf=Transpose[hnf];];
{umat,hnf,vmat}]

divides[a_,b_]:=GCD[a,b]===a

smithNormalForm[mat_?MatrixQ]:=Module[{uu,dd,vv,diags,gcd,col=0,dim,tmpu,tmpv},
{uu,dd,vv}=diagonalize[mat];
diags=Select[Flatten[dd],#!=0&];
dim=Length[diags];
While[col+1<dim,col++;
If[divides[diags[[col]],GCD[Apply[Sequence,Drop[diags,col]]]],Continue[]];
vv=Transpose[vv];
Do[dd[[j,col]]=diags[[j]];
vv[[col]]+=vv[[j]],{j,col+1,dim}];
vv=Transpose[vv];
{tmpu,dd,tmpv}=diagonalize[dd];
uu=tmpu.uu;
vv=vv.tmpv;
diags=Select[Flatten[dd],#!=0&];];
{uu,dd,vv}]


(* ::Section:: *)
(*Rigidity Matrix Functions*)


(* Fixed lattice matrix code *)
(* if fixedperiodic is true how do we deal with z's?? *)
(* convention for "lattice" columns agrees with papers *)

RigidityMatrix[z_,posns_,basis_,edgedat_,fixedperiodic_:False]:=
Module[{numbonds=Length[edgedat],qdim=Length[z],dim=Length[posns[[1]]],bcomponent,bvec,
numpart=Length[posns],part1,part2,ebond,kb,lattchange,zm,edatExtend,k,j},
SparseArray[Flatten[Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=1;(*edgedat[[j,3]];*)
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edgedat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
zm=Product[z[[k]]^edatExtend[[k]],{k,qdim}];
ebond=-posns[[part1]]+(posns[[part2]]+lattchange); (* sign convention from malestein theran *)
(* ebond=ebond/Norm[ebond];*)
If[part1!=part2,(Join[
Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],
Table[{j,dim (part2-1)+k}->ebond[[k]] zm,{k,dim}],
If[fixedperiodic,Flatten[
Table[{j,dim numpart+(bvec-1) dim+bcomponent}->edatExtend[[bvec]] (ebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}]]
,{}]
]),
(* part1\[Equal]part2*)
Join[Table[{j,dim (part1-1)+k}->-ebond[[k]](1-zm),{k,dim}],
If[fixedperiodic,Flatten[
Table[{j,dim numpart+(bvec-1) dim+bcomponent}->edatExtend[[bvec]](ebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}]]
,{}]]
],
{j,numbonds}]]
,{numbonds,dim numpart+If[fixedperiodic,qdim*dim,0]}]
];

CompatibilityMatrix[z_,posns_,basis_,edgedat_,fixedperiodic_:False]:=
Module[{numbonds=Length[edgedat],qdim=Length[z],dim=Length[posns[[1]]],bcomponent,bvec,
numpart=Length[posns],part1,part2,ebond,lattchange,zm,edatExtend,k,j},
SparseArray[Flatten[Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edgedat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
zm=Product[z[[k]]^edatExtend[[k]],{k,qdim}];
ebond=-posns[[part1]]+(posns[[part2]]+lattchange); (* sign convention from malestein theran *)
(* unit vectors *)
ebond=ebond/Norm[ebond];
If[part1!=part2,(Join[
Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],
Table[{j,dim (part2-1)+k}->ebond[[k]] zm,{k,dim}],
If[fixedperiodic,Flatten[
Table[{j,dim numpart+(bvec-1) dim+bcomponent}->edatExtend[[bvec]] (ebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}]]
,{}]
]),
(* part1\[Equal]part2*)
Join[Table[{j,dim (part1-1)+k}->-ebond[[k]](1-zm),{k,dim}],
If[fixedperiodic,Flatten[
Table[{j,dim numpart+(bvec-1) dim+bcomponent}->edatExtend[[bvec]](ebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}]]
,{}]]
],
{j,numbonds}]]
,{numbonds,dim numpart+If[fixedperiodic,qdim*dim,0]}]
];

NRigidityMatrix[z_?(VectorQ[#,NumericQ]&),posns_,basis_,edgedat_,fixedperiodic_:False]:=
RigidityMatrix[z,posns,basis,edgedat,fixedperiodic];

NCompatibilityMatrix[z_?(VectorQ[#,NumericQ]&),posns_,basis_,edgedat_,fixedperiodic_:False]:=
CompatibilityMatrix[z,posns,basis,edgedat,fixedperiodic];

IncidenceMat[z_,edgedat_,dim_,fixedperiodic_:False]:=
Module[{numbonds=Length[edgedat],qdim=Length[z],bvec,
numpart=Max[edgedat[[All,1]]],part1,part2,zm,edatExtend,k,j},
ArrayFlatten[Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edgedat[[j,2]]]}]];
zm=Product[z[[k]]^edatExtend[[k]],{k,qdim}];
If[part1!=part2,Join[Table[
If[k==part1,-IdentityMatrix[dim],
If[k==part2, zm IdentityMatrix[dim],0]],{k,numpart}],
If[fixedperiodic,
Table[edatExtend[[bvec]]IdentityMatrix[dim],{bvec,qdim}],{}]
],
(* part1\[Equal]part2*)
Join[Table[If[k==part1,-(1-zm)IdentityMatrix[dim],0],{k,numpart}],
If[fixedperiodic,
Table[edatExtend[[bvec]]IdentityMatrix[dim]
,{bvec,qdim}]
,{}]]
],
{j,numbonds}]]
];



(* Generalized periodic Rigidity matrix*)

(* for fixed periodicity, the derivative of the transformation matrices is encoded in the last 
qdim(dim(dim+1)) columns of the matrix as the nonredundant components of an element of 
the Lie algebra to the dim-dimensional affine group

Since T1.T2 = T2.T1 for all pairs, if t1 and t2 are the infinitesimal changes in T1 and T2, 
we must have:

t1.T2 + T1.t2 = T2.t1 + t2.T1 

Fortunately, this is a linear condition on t1 and t2

Order of components: for each j = 1 to qdim, 
first the dim components of the translation
then the dim^2 components of the transformation matrix

*)

(* With fixedperiodic, before taking the nullspace, may want to adjoin rows that constrain
the entries of the derivatives of the transformation matrices, e.g. the commutation condition above,
forcing them to be antisymmetric, etc.
 *)
Clear[RigidityMatrixT]

RigidityMatrixT[z_,posns_,transformations_,edgedat_,fixedperiodic_:False]:=
Module[{numbonds=Length[edgedat],qdim=Length[transformations],dim=Length[posns[[1]]],bcomponent,
bvec,bmatrixcomponent,bcomponent2,bcoeff,tebond,
numpart=Length[posns],part1,part2,ebond,kb,lattchange,zm,edatExtend,tmat,pv,
k,j,i,ebondrot},
SparseArray[Flatten[Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=1;(*edgedat[[j,3]];*)
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edgedat[[j,2]]]}]];
zm=Product[z[[k]]^edatExtend[[k]],{k,qdim}];
(* assuming that all matrices in transf commute... *)
tmat=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,qdim}]; (* maybe could memoize *)
pv=tmat.Join[posns[[part2]],{1}];
ebond=-posns[[part1]]+pv[[1;;dim]]; (* sign convention from malestein theran *)
ebondrot=ebond.tmat[[;;dim,;;dim]];
(* ebond=ebond/Norm[ebond];*)
If[part1!=part2,
Join[Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],
Table[{j,dim (part2-1)+k}->zm ebondrot[[k]],{k,dim}],
If[fixedperiodic,Flatten[
Join[(* translational components *)
tebond=Sum[MatrixPower[tmat[[;;dim,;;dim]],l],{l,edatExtend[[bvec]]-1}].tmat[[;;dim,dim+1]]
+tmat[[;;dim,dim+1]];
Table[{j,dim numpart+(bvec-1) dim(dim+1)+bcomponent}->edatExtend[[bvec]] (tebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}],
(* transformation matrix components  *)
Table[
bcomponent2=Ceiling[bmatrixcomponent/dim];
bcomponent=Mod[bmatrixcomponent,dim,1];
bcoeff=(ebond[[bcomponent]])(posns[[part2,bcomponent2]]);
{j,dim numpart+(bvec-1) dim(dim+1)+dim+bmatrixcomponent}->edatExtend[[bvec]]bcoeff
,{bvec,qdim},{bmatrixcomponent,dim^2}]
]]
,{}]]
,
(* part1\[Equal]part2*)
Join[Table[{j,dim (part1-1)+k}->-ebond[[k]]+zm ebondrot[[k]],{k,dim}],
If[fixedperiodic,Flatten[
Join[(* translational components *)
Table[{j,dim numpart+(bvec-1) dim(dim+1)+bcomponent}->edatExtend[[bvec]] (ebond[[bcomponent]])
,{bvec,qdim},{bcomponent,dim}],
(* transformation matrix components  *)
Table[
bcomponent2=Ceiling[bmatrixcomponent/dim];
bcomponent=Mod[bmatrixcomponent,dim,1];
bcoeff=(ebond[[bcomponent]])(posns[[part2,bcomponent2]]);
{j,dim numpart+(bvec-1) dim(dim+1)+dim+bmatrixcomponent}->edatExtend[[bvec]]bcoeff
,{bvec,qdim},{bmatrixcomponent,dim^2}]
]]
,{}]]
],
{j,numbonds}]]
,{numbonds,dim numpart+If[fixedperiodic,qdim*dim(dim+1),0]}]
];

NRigidityMatrixT[z_?(VectorQ[#,NumericQ]&),posns_,transformations_,edgedat_,fixedperiodic_:False]:=
RigidityMatrixT[z,posns,transformations,edgedat,fixedperiodic];

RigidityMatrix3I[z_,posns_,rodrig_,transl_,edgedat_,fixedperiodic_:False]:=Module[{transformations,A},
(* cauchy transform *)
transformations=Table[
A={{0,rodrig[[j,3]],-rodrig[[j,2]]},{-rodrig[[j,3]],0,rodrig[[j,1]]},
{rodrig[[j,2]],-rodrig[[j,1]],0}};
ArrayFlatten[{{(IdentityMatrix[3]-A).Inverse[(IdentityMatrix[3]+A)],
Transpose[{transl[[j]]}]},{0,1}}],{j,Length[rodrig]}];
RigidityMatrixT[z,posns,transformations,edgedat,fixedperiodic]]


EdgeLengthsSq[posns_,basis_,edgedat_]:=Module[{part1,part2,kb,lattchange,qdim=Length[basis],ebond,
numbonds=Length[edgedat],edatExtend,j},
Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=edgedat[[j,3]];
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edgedat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
ebond=-posns[[part1]]+(posns[[part2]]+lattchange); (* sign convention from malestein theran *)
Norm[ebond]^2
,
{j,numbonds}]];


EdgeLengthsSqT[posns_,transf_,edgedat_]:=Module[{part1,part2,kb,qdim=Length[transf],ebond,
numbonds=Length[edgedat],edatExtend,tmat,pv,dim=Length[posns[[1]]],j,i},
Table[part1=edgedat[[j,1,1]];
part2=edgedat[[j,1,2]];
kb=edgedat[[j,3]];
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],Table[0,{qdim-Length[edgedat[[j,2]]]}]];
tmat=Dot@@Table[MatrixPower[transf[[i]],edatExtend[[i]]],{i,qdim}]; (* maybe could memoize *)
pv=tmat.Join[posns[[part2]],{1}];
ebond=-posns[[part1]]+pv[[;;dim]]; (* sign convention from malestein theran *)
Norm[ebond]^2
,
{j,numbonds}]];

EdgeLengthsSq3I[posns_,rodrig_,transl_,edgedat_]:=Module[{transformations,A},
(* cauchy transform *)
transformations=Table[
A={{0,rodrig[[j,3]],-rodrig[[j,2]]},{-rodrig[[j,3]],0,rodrig[[j,1]]},
{rodrig[[j,2]],-rodrig[[j,1]],0}};
ArrayFlatten[{{(IdentityMatrix[3]-A).Inverse[(IdentityMatrix[3]+A)],
Transpose[{transl[[j]]}]},{0,1}}],{j,Length[rodrig]}];
EdgeLengthsSqT[posns,transformations,edgedat]]


(* don't trust this right now in full generality - gauge choices made in rigidity matrix functions may be inconsistent with it *)

NetDipole[posns_,basis_,edgedat_]:=Module[{vertcont,edgecont,dim=Length[posns[[1]]],qdim=Length[basis],
nsp=NullSpace[basis],edatExtend,j},
vertcont=dim(Sum[posns[[j]],{j,Length[posns]}]);
edgecont=Sum[
edatExtend=Join[edgedat[[j,2,1;;Min[Length[edgedat[[j,2]]],qdim]]],Table[0,{qdim-Length[edgedat[[j,2]]]}]];
(posns[[edgedat[[j,1,1]]]]+posns[[edgedat[[j,1,2]]]]+edatExtend.basis)/2
,{j,Length[edgedat]}];
(Inverse[Transpose[Join[basis,nsp]]].(vertcont-edgecont))[[1;;qdim]]
];


KLWinding[z_,latticep_,basis_,latticeE_,cycle_,t_]:=Module[{powmat,w1,w2,zz},
powmat=RigidityMatrix[z,latticep,basis,latticeE];
zz=Det[powmat]/.cycle;
w1=NIntegrate[Im[D[Log[zz],t]],{t,0,2\[Pi]}];
-w1/(2\[Pi])
];


KLPolarization[latticep_,basis_,latticeEdat_,cyclesorigin0_:{}]:=
Module[{powmat,w,zz,k,qdim=Length[basis],z,cycle,t,cyclesorigin},
(* need both cyclesorigin0 and cyclesorigin because Mathematica's optional arguments are no longer variables *)
If[Length[cyclesorigin0]!=qdim, cyclesorigin = Table[-1,{qdim}],cyclesorigin=cyclesorigin0];
powmat=RigidityMatrix[Table[z[j],{j,qdim}],latticep,basis,latticeEdat];
w=Table[
cycle=Table[z[k]->If[k!=j,cyclesorigin[[k]],Exp[I t]],{k,qdim}];
zz=Det[powmat]/.cycle;
NIntegrate[Im[D[Log[zz],t]],{t,0,2\[Pi]}]
,{j,qdim}];
-w/(2\[Pi])
];


(* these are not correct: the true dynamical matrix should be R^T(-z).R(z) *)

(* "dynamical matrix" shorthand function *)
DynMat[rig_,kmat_:{}]:=Module[{},If[kmat=={},ConjugateTranspose[rig].rig,
ConjugateTranspose[rig].kmat.rig]];

(* "hamiltonian matrix" shorthand function *)
HMat[rig_]:=ArrayFlatten[{{0,ConjugateTranspose[rig]},{rig,0}}];


(* ::Section:: *)
(*Stress matrices*)


(* stress matrix function *)
StressMatrix[stress_,edat_,dim_,fixedperiodic_:False]:=Module[{j,inc,
qdim=Max[Length/@edat[[All,2]]]},
inc=IncidenceMat[Table[1,{qdim}],edat,dim,fixedperiodic];
Transpose[inc].DiagonalMatrix[Flatten[Table[{stress[[j]]}
,{j,Length[stress]},{dim}]]].inc
];



(* ::Section:: *)
(*Elastic tensor*)


symmetricindexlist[dim_]:=Flatten[Table[
Table[{j,j+(i-1)},{j,dim-i+1}]
,{i,dim}],1]

(* ordering of indices in elastic tensor in dim dimensions *)
fourthrankindices[dim_]:=Module[{sil=symmetricindexlist[dim]},Table[
Subscript[\[Epsilon], sil[[is]]] Subscript[\[Epsilon], sil[[js]]]
,{is,dim (dim+1)/2},{js,dim (dim+1)/2}]]


(* let k0 be a list of spring constants, possibly including 0's *)
ElasticTensor[pos_,basis_,edat0_,k0_:{}]:=Module[{k,qdim=Length[basis],
dim=Length[pos[[1]]],E=Length[edat0],numparts=Length[pos],C,U,\[CapitalSigma],Vs,is,js,
presym,Eafflist,Eafflist2,
symmetricindex,i,j,pair1,pair2,kk,matA,matB,matC,matD,proj,
part1,part2,edatExtend,lattchange,ebond,ebondlist,eps=10^-14,numss,nonzeros,edat},

(* kk is a matrix! *)
kk=If[Length[k0]!=E||Depth[k0]!=2,Print["Assuming all spring constants are 1"];
edat=edat0;IdentityMatrix[E],
(* remove edges with sufficiently small spring constant *)
nonzeros=Position[k0,(x_/;(x>eps)||(Not[NumericQ[x]]))][[2;;-2]];
edat=edat0[[Flatten[nonzeros]]];
E=Length[nonzeros];
DiagonalMatrix[Extract[k0,nonzeros]]
];

ebondlist=Table[Null,{E}];
(* compute compatibility matrix at q=0 and save the vector of extensions "ebondlist" *)
C=SparseArray[Flatten[Table[
part1=edat[[j,1,1]];
part2=edat[[j,1,2]];
edatExtend=Join[edat[[j,2,1;;Min[Length[edat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
ebond=-pos[[part1]]+(pos[[part2]]+lattchange); (* sign convention from malestein theran *)
(* unit vectors *)
ebondlist[[j]]=ebond;
ebond=ebond/Norm[ebond];
If[part1!=part2,
Join[
Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],Table[{j,dim (part2-1)+k}->ebond[[k]] ,{k,dim}]
],
(* part1\[Equal]part2*)
Table[{j,dim (part1-1)+k}->0,{k,dim}]
],
{j,E}]]
,{E,dim numparts}];

(* get basis for space of ss *)
U=NullSpace[Transpose[C]];(*Print[Length[U]];*)
(* now we project k^-1 onto ss space, creates a LinearSolveFunction which can act on a vector *)
(* hopefully a better way of computing MatrixInverse[U.MatrixInverse[k].Transpose[U]]*)
kk=LinearSolve[U.LinearSolve[kk,Transpose[U]]];

(*Print[kk[IdentityMatrix[Length[U]]]];*)

(* a list of pairs of indices *)
symmetricindex=Flatten[Table[
Table[{j,j+(i-1)},{j,dim-i+1}]
,{i,dim}],1];
(* compute coefficients of Subscript[\[Epsilon], ij] in the components of Subscript[E, aff] (indexed by j) *)
(* separate into different lists, indexed by "is" *)
Eafflist=Table[
pair1=symmetricindex[[is]];
ebond=ebondlist[[j]];
ebond[[pair1[[1]]]]ebond[[pair1[[2]]]]/Norm[ebond]
,{is,dim (dim+1)/2},{j,E}];
(* projection onto self-stress space *)
(*proj=ArrayFlatten[{Join[Table[0,{E-numss}],{IdentityMatrix[numss]}]}].Transpose[U];*)
proj=U;
Eafflist2=Table[proj.Eafflist[[is]],{is,dim (dim+1)/2}];
 (*Eafflist2=Transpose[proj.Transpose[Eafflist]];*)
(* store components of the elastic tensor in an upper triangular matrix *)
presym=Table[
If[is<=js,
Eafflist2[[is]].kk[Eafflist2[[js]]]
,0]
,{is,dim (dim+1)/2},{js,dim (dim+1)/2}];
(* reorganize upper triangular matrix into a symmetric matrix; probably inefficient here *)
Table[presym[[Min[is,js],Max[is,js]]]
,{is,dim (dim+1)/2},{js,dim (dim+1)/2}]
]


(* currently broken for undercoordinated / unstable systems *)

(* let k0 be a list of spring constants, possibly including 0's *)
ElasticTensor2[pos_,basis_,edat0_,k0_:{}]:=Module[{k,qdim=Length[basis],
dim=Length[pos[[1]]],E=Length[edat0],numparts=Length[pos],C,U,\[CapitalSigma],Vs,is,js,
presym,Eafflist,Eafflist2,
symmetricindex,i,j,pair1,pair2,kk,matA,matB,matC,matD,proj,
part1,part2,edatExtend,lattchange,ebond,ebondlist,eps=10^-14,numss,nonzeros,edat},

(* kk is a matrix! *)
kk=If[Length[k0]!=E||Depth[k0]!=2,Print["Assuming all spring constants are 1"];
edat=edat0;IdentityMatrix[E],
(* remove edges with sufficiently small spring constant *)
nonzeros=Position[k0,(x_/;(x>eps)||(Not[NumericQ[x]]))][[2;;-2]];
edat=edat0[[Flatten[nonzeros]]];
E=Length[nonzeros];
DiagonalMatrix[Extract[k0,nonzeros]]
];

ebondlist=Table[Null,{E}];
(* compute compatibility matrix at q=0 and save the vector of extensions "ebondlist" *)
C=SparseArray[Flatten[Table[
part1=edat[[j,1,1]];
part2=edat[[j,1,2]];
edatExtend=Join[edat[[j,2,1;;Min[Length[edat[[j,2]]],qdim]]],
Table[0,{qdim-Length[edat[[j,2]]]}]];
lattchange=If[qdim>0,edatExtend.basis,0];
ebond=-pos[[part1]]+(pos[[part2]]+lattchange); (* sign convention from malestein theran *)
(* unit vectors *)
ebondlist[[j]]=ebond;
ebond=ebond/Norm[ebond];
If[part1!=part2,
Join[
Table[{j,dim (part1-1)+k}->-ebond[[k]],{k,dim}],Table[{j,dim (part2-1)+k}->ebond[[k]] ,{k,dim}]
],
(* part1\[Equal]part2*)
Table[{j,dim (part1-1)+k}->0,{k,dim}]
],
{j,E}]]
,{E,dim numparts}];
(* previous try using Schur complement by hand *)

(* compute SVD of compatibility matrix *)
{U,\[CapitalSigma],Vs}=SingularValueDecomposition[C];
(* get number of self-stresses at q = 0*)
(* numss can end up negative, which is bad *)
numss=Length[Select[Diagonal[Normal[\[CapitalSigma]]],Abs[N[#]]<eps&]]+E-dim numparts;
kk=If[Length[k0]==0,IdentityMatrix[numss],
(* Schur complement of k0, after rotating into stress eigenvector basis with Vs and Transpose[Vs].
The Schur complement for a matrix in block form {{A,B},{C,D}} is 
A - B D^{-1} C .
*)
kk=Transpose[U].kk.U;
(*Print[kk];
Print[\[CapitalSigma]];
Print[E];
Print[numss];*)
matA=kk[[E-numss+1;;E,E-numss+1;;E]];
If[E==numss,matA,
matB=kk[[E-numss+1;;E,;;E-numss]];
matC=kk[[;;E-numss,E-numss+1;;E]];
matD=kk[[;;E-numss,;;E-numss]];
matA-matB.LinearSolve[matD,matC]]
];
(* don't we need to rotate back? *)
(* something above was wrong. kk could end up with negative eigenvalues?? *)
(* I believe this is fixed now.  Unclear which is more efficient *)
(*Print[kk];*)

(* a list of pairs of indices *)
symmetricindex=Flatten[Table[
Table[{j,j+(i-1)},{j,dim-i+1}]
,{i,dim}],1];
(* compute coefficients of Subscript[\[Epsilon], ij] in the components of Subscript[E, aff] (indexed by j) *)
(* separate into different lists, indexed by "is" *)
Eafflist=Table[
pair1=symmetricindex[[is]];
ebond=ebondlist[[j]];
ebond[[pair1[[1]]]]ebond[[pair1[[2]]]]/Norm[ebond]
,{is,dim (dim+1)/2},{j,E}];
(* projection onto self-stress space *)
proj=ArrayFlatten[{Join[Table[0,{E-numss}],{IdentityMatrix[numss]}]}].Transpose[U];
(*proj=U;*)
Eafflist2=Table[proj.Eafflist[[is]],{is,dim (dim+1)/2}];
 (*Eafflist2=Transpose[proj.Transpose[Eafflist]];*)
(* store components of the elastic tensor in an upper triangular matrix *)
presym=Table[
If[is<=js,
Eafflist2[[is]].kk.Eafflist2[[js]]
,0]
,{is,dim (dim+1)/2},{js,dim (dim+1)/2}];
(* reorganize upper triangular matrix into a symmetric matrix; probably inefficient here *)
Table[presym[[Min[is,js],Max[is,js]]]
,{is,dim (dim+1)/2},{js,dim (dim+1)/2}]
]


(* ::Section:: *)
(*Constraints and Pebble related*)


ConstraintRows[numverts_,pinnedverts_,template_]:=Module[{j,k,dim=Length[template[[1]]]},
Table[Flatten[Table[
If[k==pinnedverts[[j]],template[[j]],
Table[0,{dim}]]
,{k,numverts}]]
,{j,Length[pinnedverts]}]];


PinnedRows[numverts_,verts_,dim_]:=Module[{k,unitvec},
Flatten[Table[
unitvec=Table[UnitVector[dim,k],{Length[verts]}];
ConstraintRows[numverts,verts,unitvec],
{k,dim}],1]];


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
];

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
infinitesimal2drotationmode[pos_,basis_:{},cent_:{0,0}]:=Module[{j,numparts=Length[pos],basisrot,posrot},
posrot=Table[{(pos[[j,2]]-cent[[2]]),-(pos[[j,1]]-cent[[1]])},{j,numparts}];
basisrot=Table[{basis[[j,2]],-basis[[j,1]]},{j,Length[basis]}];
Join[Flatten[posrot],If[Length[basis]>0,
Flatten[Table[basisrot[[i]],
{i,Length[basis]}]]
,{}
]]
];

infinitesimalrotation[origin_,posns_]:=Module[{j,diff},
Flatten[Table[
diff=posns[[j]]-origin;
{-diff[[2]],diff[[1]]},{j,Length[posns]}]]];

getnontriv2D[pos_,basis_,edgedat_]:=Module[{pmtestk,testrotk,transx,transy,numatoms=Length[pos]},
pmtestk=Normal[RigidityMatrix[Table[1,{Length[basis]}],pos,basis,edgedat,True]];
transx=Flatten[Join[Table[{1,0},{numatoms}],Table[0,{2Length[basis]}]]];
transy=Flatten[Join[Table[{0,1},{numatoms}],Table[0,{2Length[basis]}]]];
testrotk=infinitesimal2drotationmode[pos,basis];
NullSpace[Join[pmtestk,{transx,transy,testrotk}]][[1]]];

getnontriv2Dall[pos_,basis_,edgedat_]:=Module[{pmtestk,testrotk,transx,transy,numatoms=Length[pos]},
pmtestk=Normal[RigidityMatrix[Table[1,{Length[basis]}],pos,basis,edgedat,True]];
transx=Flatten[Join[Table[{1,0},{numatoms}],Table[0,{2Length[basis]}]]];
transy=Flatten[Join[Table[{0,1},{numatoms}],Table[0,{2Length[basis]}]]];
testrotk=infinitesimal2drotationmode[pos,basis];
NullSpace[Join[pmtestk,{transx,transy,testrotk}]]];

getnontriv2Dmat[pos_,basis_,edgedat_]:=Module[{pmtestk,testrotk,transx,transy,numatoms=Length[pos]},
pmtestk=Normal[RigidityMatrix[Table[1,{Length[basis]}],pos,basis,edgedat,True]];
transx=Flatten[Join[Table[{1,0},{numatoms}],Table[0,{2Length[basis]}]]];
transy=Flatten[Join[Table[{0,1},{numatoms}],Table[0,{2Length[basis]}]]];
testrotk=infinitesimal2drotationmode[pos,basis];
Join[pmtestk,{transx,transy,testrotk}]];

getnontriv2Dflat[flatvec_?(VectorQ[#,NumericQ]&),edgedat_]:=Module[{pmtestk,testrotk,transx,transy,
numatoms,pos,basis,nsp,nspp,bigrig,bigrig2,j},
numatoms=(Length[flatvec]-4)/2;
pos=Partition[flatvec[[1;;2numatoms]],2];
basis={flatvec[[-4;;-3]],flatvec[[-2;;-1]]};
pmtestk=Normal[RigidityMatrix[{1,1},pos,basis,edgedat,True]];
transx=Flatten[Join[Table[{1,0},{numatoms}],Table[0,{4}]]];
transy=Flatten[Join[Table[{0,1},{numatoms}],Table[0,{4}]]];
testrotk=infinitesimal2drotationmode[pos,basis];
bigrig=Join[pmtestk,{transx,transy,testrotk}];
bigrig2=bigrig[[1;;-2,1;;2numatoms]];
nspp=NullSpace[bigrig2];
If[Length[nspp]>0,bigrig=Join[bigrig,nspp=Table[Join[nspp[[j]],{0,0,0,0}],{j,Length[nspp]}]]];
nsp=NullSpace[bigrig];
Join[nspp,nsp]
];


(* some functions giving constraint rows on the deformations of transformation matrices *)

(* ordering of columns, first the dim components of translations, then the dim^2 components of the 
transformation matrix;

{i,j} are the indices of a matrix entry (row, column), 1\[LessEqual]i\[LessEqual]dim, 1\[LessEqual]j\[LessEqual]dim+1
 *)
coeffindexT[i_,j_,dim_]:=Module[{},
If[j==dim+1,i,
i dim+j
]
];

(* 

t1.T2 + T1.t2 = T2.t1 + t2.T1 

a_kl.B_lm + A_kl.b_lm - B_kl.a_lm - b_kl.A_lm = 0

 *)
commuteconstraintT[numparts_,transformations_]:=Module[
{qdim=Length[transformations],dim,pairtab,temp,datavec
i1,i2,j,k,l,m,coeffindex,rowind,colind,maxcol},
temp=Dimensions[transformations[[1]]];
If[(temp[[1]]!=temp[[2]]),Print["transformation matrix has wrong shape"];Abort[];,
dim=temp[[1]]-1];(*Print[dim];*)
maxcol=dim numparts+qdim dim (dim+1);
(* one set of rows for each pair *)
pairtab=Subsets[Range[qdim],{2}];Print[pairtab];
Table[{i1,i2}=pairtab[[j]];
Table[rowind=(j-1)dim(dim+1)+(m-1)(dim)+k;
datavec=Table[0,{dim numparts+qdim dim(dim+1)}];
Do[
{(* a_kl entry *)
If[l!=m,colind=dim numparts+(i1-1)dim(dim+1)+coeffindexT[k,l,dim];
datavec[[colind]]+=transformations[[i2,l,m]];
If[colind>maxcol,Print["too big akl ",i1,i2,k,l,m];];,
(* a_km entry special *)
colind=dim numparts+(i1-1)dim(dim+1)+coeffindexT[k,m,dim];
datavec[[colind]]+=
transformations[[i2,m,m]]-transformations[[i2,k,k]];
If[colind>maxcol,Print["too big akm ",i1," ",i2," ",k," ",l," ",m];];
],
(* a_lm entry *)
If[l!=k,colind=dim numparts+(i1-1)dim(dim+1)+coeffindexT[l,m,dim];
datavec[[colind]]+=transformations[[i2,k,l]],{}];
If[colind>maxcol,Print["too big alm ",i1," ",i2," ",k," ",l," ",m];];,
(* b_kl entry *)
If[l!=m,colind=dim numparts+(i2-1)dim(dim+1)+coeffindexT[k,l,dim];
datavec[[colind]]+=transformations[[i1,l,m]];
If[colind>maxcol,Print["too big bkl ",i1," ",i2," ",k," ",l," ",m];];,
(* b_km entry special *)
colind=dim numparts+(i2-1)dim(dim+1)+coeffindexT[k,m,dim];
datavec[[colind]]+=
transformations[[i1,m,m]]-transformations[[i1,k,k]];
If[colind>maxcol,Print["too big bkm ",i1," ",i2," ",k," ",l," ",m];];
],
(* b_lm entry *)
If[l!=k,colind=dim numparts+(i2-1)dim(dim+1)+coeffindexT[l,m,dim];
datavec[[colind]]+=transformations[[i1,k,l]],{}];
If[colind>maxcol,Print["too big blm ",i1," ",i2," ",k," ",l," ",m];];
}
,{l,dim+1}];datavec
,{k,dim},{m,dim+1}]
,{j,Length[pairtab]}]]
(*,
{Length[pairtab]dim(dim+1),dim numparts+qdim dim (dim+1)}
]]*)


(* for isometries, need a function to ensure that the dim^2 components correspond to
entries of a matrix in so(d) *)


(* need this to be cromulent with CoveringFrameworkVerts and CoveringFrameworkEdges *)
CoveringMotion[mode_,cover_,dim0_:0,periodic_:False]:=Module[{i,j,dim,qdim=Length[cover],
numparts,tabspec,m,ind},
dim=If[dim0!=0,dim0,qdim];
(* dim*number of particles + dim qdim = length of mode vector*)
If[Mod[(Length[mode]-dim qdim),dim]!=0,Print["bad mode length"];Abort[]];
numparts=(Length[mode]-dim qdim)/dim; (* y then x *)
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Join[Flatten[
Table[
Table[
(* affine contribution from last components of mode *)
(* infinitesimal change of jth basis vector *)
Sum[ind=dim numparts+dim (j-1);
mode[[ind+1;;ind+dim]]*m[j],{j,qdim}]
(* internal components of mode *)
+mode[[dim (i-1)+1;;dim (i-1)+dim]],
{i,numparts}],
##]&@@tabspec (* specification of table, dim copies of loops from 0 to cover-1 *)
],
If[periodic,
Flatten[Table[
ind=dim numparts+dim(j-1);
cover[[j]]mode[[ind+1;;ind+dim]],{j,qdim}]],{}]
]
];

(* need this to be cromulent with CoveringFrameworkVerts and CoveringFrameworkEdges *)
CoveringMotionz[z_,mode_,cover_,dim0_:0]:=Module[{i,j,dim,qdim=Length[cover],
numparts,tabspec,m,ind,mult},
dim=If[dim0!=0,dim0,qdim];
(* dim*number of particles = length of mode vector*)
If[Mod[(Length[mode]),dim]!=0,Print["bad mode length"];Abort[]];
numparts=(Length[mode])/dim; (* y then x *)
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Flatten[
Table[
Table[
(* contribution from z; take real part by default *)
mult=Re[Product[z[[j]]^m[j],{j,qdim}]];
(* internal components of mode *)
mult mode[[dim (i-1)+1;;dim (i-1)+dim]],
{i,numparts}],
##]&@@tabspec (* specification of table, dim copies of loops from 0 to cover-1 *)
]
];


SubtractTranslations[mode_,dim_,periodicdim_:0]:=Module[{modeinternal,modeguest,avgtranslation,numparts},
If[periodicdim>0,
modeinternal=mode[[;;-periodicdim dim-1]];
modeguest=mode[[-periodicdim dim;;]];
,
modeinternal=mode;
modeguest={};
];
numparts=(Length[modeinternal]/dim);
avgtranslation=Total[Partition[modeinternal,dim]]/numparts;
Join[modeinternal-Flatten[Table[avgtranslation,{numparts}]],modeguest]
]


(* this should yield the elastic displacements in a spring network *)
(* Lap is the dynamical matrix *)
(* bvtr is a list of indices of particles whose displacements will be specified by u *)
(* u is the list of applied displacements *)
HarmonicExtension[Lap_,bvtr_,u_,dim_:2]:=Module[{j,l=Dimensions[Lap][[2]]/dim,
inter,dinter,cinter,matB,matC,fI,ans},
(* need to be careful with "Complement" because does not preserve ordering *)
inter=Complement[Table[j,{j,l}],bvtr];
dinter=PosVecIndices[inter,dim];
cinter=PosVecIndices[bvtr,dim];
(* somehow slower if u is sparse????*)
(*matB=If[toggle\[Equal]1,SparseArray[Lap[[dinter,cinter]].u],Lap[[dinter,cinter]].u];*)
matB=Lap[[dinter,cinter]].u;
(* dissatisfying that taking determinant here is the only way to see whether we have rigidity inside*)
matC=Lap[[dinter,dinter]];
If[Chop[Det[matC]]==0,
Print["Rank deficient; system is floppy"];,
(*fI=-Inverse[matC].matB.u;*)
(*fI=If[toggle\[Equal]1,-LinearSolve[matC,matB,Method\[Rule]"Krylov"],-LinearSolve[matC,matB]];*)
fI=-LinearSolve[matC,matB];
ans=Table[0,{dim l}];
Do[ans[[dinter[[j]]]]=fI[[j]];,{j,Length[fI]}];
Do[ans[[cinter[[j]]]]=u[[j]];,{j,Length[u]}];
ans]
];

(* Dirichlet to Neumann operator *)
DtN[Lap_,bvtr_,dim_:2]:=Module[{j,l=Dimensions[Lap][[1]]/dim,inter,dinter,cinter,matA,matB,matC,matD},
inter=Complement[Table[j,{j,l}],bvtr];
dinter=PosVecIndices[inter,dim];
cinter=PosVecIndices[bvtr,dim];
matA=Lap[[cinter,cinter]];
matB=Lap[[cinter,dinter]];
matC=Lap[[dinter,cinter]];
matD=Lap[[dinter,dinter]];
(* Schur complement *)
(*matA-matB.Inverse[matD].matC *)
matA-matB.LinearSolve[matD,matC]
];


(*pos slope, zero slope, neg slope line-localized modes for untwisted kagome*)
poslinemode[i_,m_,n_]:=Module[{j,d=Table[0,{6m n}],loc},
Do[loc=3n(i-1)+3(j-1)+2;
d[[2loc-1]]=3/4;
d[[2loc]]=Sqrt[3]/4;
d[[2loc+1]]=0;
d[[2loc+2]]=Sqrt[3]/2;,{j,n}];d];

zerolinemode[i_,m_,n_]:=Module[{j,d=Table[0,{6m n}],loc},
Do[loc=3(i-1)+3n(j-1)+1;
d[[2loc-1]]=-(3/4);
d[[2loc]]=-(Sqrt[3]/4);
d[[2loc+3]]=-(3/4);
d[[2loc+4]]=Sqrt[3]/4;,{j,m}];d];

neglinemode[i_,m_,n_]:=Module[{j,d=Table[0,{6m n}],loc},
Do[loc=If[i<m+n-i,3(i-1)+3(n-1)(j-1)+1,3m n-3(m+n-i)-3(n-1)(j-1)+1];
d[[2loc-1]]=0;
d[[2loc]]=-(Sqrt[3]/2);
d[[2loc+1]]=3/4;
d[[2loc+2]]=-(Sqrt[3]/4);,{j,Min[m+n-i,i]}];d];


(* ::Section:: *)
(*Some basic 2 D lattices*)


(* ::Subsection:: *)
(*vertex positions*)


(*square lattice*)
SqLattice[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{m,n},
Flatten[Table[
{m,n}+If[r>0,RandomReal[{-r,r},2],{0,0}]
,{m,0,xx-1},{n,0,yy-1}],1]];

SqLatticeSlopes[xx_,yy_,r_:0]:=(* yy better be even? *) 
Module[{m,n,slopesx=RandomReal[{-r,r},xx],slopesy=RandomReal[{-r,r},yy],time},
Flatten[Table[
time=computeintersection[{m,0},\[Pi]/2+slopesx[[m+1]],{0,n},slopesy[[n+1]]];
{0,n}+time [[2]]{Cos[slopesy[[n+1]]],Sin[slopesy[[n+1]]]}
,{m,0,xx-1},{n,0,yy-1}],1]];

(* Twist angle convention for kagome lattices has the opposite sign from that of K Sun et al PNAS 2012 *)

(* kagome in the form of a rhombus *)
KagLatticeRho[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *)Module[{m,n,i},
Flatten[Table[
{(*Mod[m+1/2.n,xx]*)m+1/2 n,Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}
+If[r>0,RandomReal[{-r,r},2],{0,0}]
+1/(2 Sqrt[3]Cos[th]) {Cos[\[Pi]/6+2 \[Pi]/3 i+th],Sin[\[Pi]/6+2 \[Pi]/3 i+th]}
,{m,1,xx},{n,0,yy-1},{i,3}],2]];

(* perturbed kagome in the form of a rhombus. The three vertices per unit cell are inscribed 
in a unit equilateral triangle (if t=0)
notation:
{s1,s2,s3} are parameters along the three edges of the equilateral triangle parallel to {1,0}, 
{-1/2,Sqrt[3]/2} and {-1/2,-Sqrt[3]/2}, respectively.

t displaces the s2 vertex in a direction perpendicular to that edge of the triangle
 *)
PKagLatticeRho[xx_,yy_,s1_,s2_,s3_,t_:0,r_:0]:=(* yy better be even? *)Module[{m,n,i},
Flatten[Table[
{(*Mod[m+1/2.n,xx]*)m+1/2 n,Sqrt[3]/2 n}
+If[r>0,RandomReal[{-r,r},2],{0,0}]
+If[i==1,(1-s3){1/2,Sqrt[3]/2},{0,0}]
+If[i==2,{s1,0},{0,0}]
+If[i==3,{1,0}+s2{-1/2,Sqrt[3]/2}+t{Sqrt[3]/2,1/2},{0,0}]
,{m,0,xx-1},{n,0,yy-1},{i,3}],2]];

(* kagome in the form of a rectangle *)
KagLatticeRec[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Module[{i,m,n},
Flatten[Table[
{m+1/2 Mod[n,2],Sqrt[3]/2 n}+{-1/4,-Sqrt[3]/12}
+If[r>0,RandomReal[{-r,r},2],{0,0}]
+1/(2 Sqrt[3]Cos[th]) {Cos[\[Pi]/6+2 \[Pi]/3 i+th],Sin[\[Pi]/6+2 \[Pi]/3 i+th]}
,{m,1,xx},{n,0,yy-1},{i,3}],2]];

(* triangular lattice in the form of rhombus *)
TriLatticeRho[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{m,n},
Flatten[Table[
{(*Mod[m+1/2.n,xx]*)m+1/2. n,Sqrt[3]/2. n}
+If[r>0,RandomReal[{-r,r},2],{0,0}]
,{m,1,xx},{n,0,yy-1}],1]];

(*triangular lattice in the form of rectangle *)
TriLatticeRec[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{m,n},
Flatten[Table[
{Mod[m+1/2. n,xx],Sqrt[3]/2. n}
+If[r>0,RandomReal[{-r,r},2],{0,0}]
,{m,1,xx},{n,0,yy-1}],1]];

(* honeycomb in the form of a rectangle *)
HoneycombLattice[xx_,yy_,r_:0]:=(* yy better be even? *) Module[{temp,x,m,n,i},
temp=Flatten[Table[
If[((Mod[m+1/2 n,xx]==0)&&(i==1))||((Mod[m+1/2 n,xx]==xx-1/2)&&(i==2)),
{},
{Mod[m+1/2 n,xx],Sqrt[3]/2 n}
+If[r>0,RandomReal[{-r,r},2],{0,0}]+(-1)^i /(2Sqrt[3]){Sqrt[3]/2,1/2}]
,{m,1,xx},{n,0,yy-1},{i,2}],2];
Replace[temp,x_List:>DeleteCases[x,{}],{0,Infinity}]
];

makekaglatticerunit[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Module[{m,n},
Flatten[Table[
{(*Mod[m+1/2.n,xx]*)m+1/2 n,Sqrt[3]/2 n}
+{-1/4,-Sqrt[3]/12}+If[r>0,RandomReal[{-r,r},2],{0,0}]
,{m,1,xx},{n,0,yy-1}],1]];

makekaglatticeunit[xx_,yy_,th_:0,r_:0]:=(* yy better be even? *) Module[{m,n},
Flatten[Table[
{Mod[m+1/2 n,xx],Sqrt[3]/2 n}
+{-1/4,-Sqrt[3]/12}+If[r>0,RandomReal[{-r,r},2],{0,0}]
,{m,1,xx},{n,0,yy-1}],1]];


(* ::Subsection:: *)
(*edge stuff*)


(* return a list of pairs of vertices corresponding to edges, first list is NN, second list is NNN *)
SqLatticeEdges[xx_,yy_]:=(* yy better be even? *) 
Module[{m,n,index=0,bondlist=Table[Null,{2xx*yy-xx-yy}],numbonds=0,
nextbondlist=Table[Null,{(xx-1)*(yy-1)}],numnextbonds=0,nextbondlistother=Table[Null,{(xx-1)*(yy-1)}]},
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
KagLatticeRecEdges[xx_,yy_]:=
Module[{i,m,n,index=0,bondlist=Table[Null,{6xx*yy}],numbonds=0,
nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],numnextbonds=0},
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
KagLatticeRhoEdges[xx_,yy_]:=
Module[{i,m,n,index=0,bondlist=Table[Null,{6xx*yy}],numbonds=0,
nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],numnextbonds=0},
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
SqLatticexperEdges[xx_,yy_]:=(* yy better be even? *) 
Module[{m,n,index=0,bondlist=Table[Null,{2xx*yy-xx}],numbonds=0,
nextbondlist=Table[Null,{(xx)*(yy-1)}],numnextbonds=0,nextbondlistother=Table[Null,{(xx)*(yy-1)}]},
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

KagLatticexperEdges[xx_,yy_]:=(* 1,2,3, go around counter clockwise from 5\[Pi]/6*)
Module[{i,m,n,index=0,bondlist=Table[Null,{6xx*yy+2yy-1}],numbonds=0,
nextbondlist=Table[Null,{3*(xx)*(yy)+xx+yy-2}],nextbondlist2=Table[Null,{3*(xx)*(yy)+xx+yy-2}],
numnextbonds=0,numnextbonds2=0},
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
boundaryvertskagr[m_,n_]:=Module[{j,horiz,minusbot,minusright,plus},
horiz=Table[{3(j-1)+1,3(j-1)+2},{j,n}];
minusbot=Table[{3(j-1)n+2,3(j-1)n+3},{j,m}];
minusright=Table[{3(m-1)n+3(j-1)+2,3(m-1)n+3(j-1)+3},{j,2,n}];
plus=Table[{3n*j-3+3,3n*j-3+1},{j,m}];
Join[horiz,minusbot,minusright,plus]];

(* just a list of vertex indices *)
boundaryvertstrir[m_,n_]:=Module[{j,left,bot,top,right},
left=Table[j,{j,n}];
bot=Table[n j+1,{j,m-1}];
top=Table[n j,{j,2,m}];
right=Table[n (m-1)+j,{j,2,n-1}];
Join[left,bot,top,right]];

splitbctrir[m_,n_,l_,b_,t_,r_]:=Module[{j,left,bot,top,right},
left=Table[l,{j,n}];
bot=Table[b,{j,m-1}];
top=Table[t,{j,2,m}];
right=Table[r,{j,2,n-1}];
Flatten[{left,bot,top,right}]];


boundaryverts2by2sq[xx_,yy_]:=Module[{m,n,ind,indout},Join[
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
Table[{getatomindex[xx,n,ind,xx,yy,4],getatomindex[xx,n,indout,xx,yy,4]},{n,yy}]]];

boundaryvertssq[xx_,yy_]:=Module[{m,n,ind,indout},Join[
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
Table[{getatomindex[m,yy,ind,xx,yy,4],getatomindex[m,yy,indout,xx,yy,4]},{m,xx}]]];


(* create lists suitable for input into the last two slots of HarmonicExtension; 
the first being the indices of the "boundary" vertices 
and the second being the actual applied forces / displacements there  *)
shearbvsq[lx_,ly_,u_:{1,0}]:=Module[{j},{(* site indices *)
Join[Table[ly(j-1)+1,{j,lx}],Table[ly*j,{j,lx}]], 
(* applied displacement components; 0 on bottom, u on top *) 
Join[Table[0,{2lx}],Flatten[Table[u,{lx}]]]}];

(* create lists suitable for input into the last two slots of HarmonicExtension; the first being the indices of the "boundary" vertices (for kagome chosen to be top and bottom row of triangles) and the second being the actual applied forces / displacements there  *)
shearbvkag[lx_,ly_,u_:{1,0}]:={(* site indices *) Join[Flatten[
Table[3ly(j-1)+i,{j,lx},{i,3}]],Flatten[Table[3ly j-3+i,{j,lx},{i,3}]]], 
(* applied displacement components; 0 on bottom, u on top *) 
Join[Table[0,{6lx}],Flatten[Table[u,{3lx}]]]}


BoundaryVerts[edgedat_,cover_,cellspec_]:=
Module[{i,j,k,qdim=Length[cover],tabspec,m,list,unitcellsize=Max[edgedat[[All,1]]]
(*,parts*)},
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
];


(* ::Section:: *)
(*Making new lattices from scratch and from old*)


(*Function to make edges for points in "pos" closer than "dis" *)
DiskGraphEdges[pos_,dis_,basis_:{},maxwinding_:1]:=
Module[{i,j,k,numverts=Length[pos],qdim=Length[basis],tabspec,m,cover},
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
];


(* make a list of vertex positions in any dimension *)
CoveringFrameworkVerts[unitcell_,latt_,cover_,r_:0]:=
Module[{i,j,qdim=Length[latt],dim=Length[unitcell[[1]]],tabspec,m},
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Flatten[
Table[
Table[
Sum[latt[[j]]*m[j],{j,qdim}]+If[r>0, RandomReal[{-r,r},dim],Table[0,{dim}]]
+unitcell[[i]],
{i,Length[unitcell]}],
##]&@@tabspec,(* specification of table, dim copies of loops from 0 to cover-1 *)
qdim]
];


(* make a list of vertex positions in any dimension from two unit cell types *)
CoveringFrameworkVertsCondition[unitcell1_,unitcell2_,latt_,cover_,m_,condition_,r_:0]:=
Module[{qdim=Length[latt],dim=Length[unitcell1[[1]]],tabspec},
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Flatten[
Table[
Table[
Sum[latt[[i]]*m[i],{i,qdim}]+If[r>0, RandomReal[{-r,r},dim],Table[0,{dim}]]
(* If condition is true, unitcell1, if condition is false, unitcell2 *)
+If[condition,unitcell1[[i]],unitcell2[[i]]],
{i,Length[unitcell1]}],
##]&@@tabspec,(* specification of table, dim copies of loops from 0 to cover-1 *)
qdim]
];


CoveringTFrameworkVerts[unitcell_,transf_,cover_]:=
Module[{i,qdim=Length[transf],dim=Length[unitcell[[1]]],tabspec,m,tmat},
tabspec=Table[{m[i],0,cover[[i]]-1},{i,qdim}];
Flatten[
Table[
(* assuming that all matrices in transf commute... *)
tmat=Dot@@Table[MatrixPower[transf[[i]],m[i]],{i,qdim}];
Dot[tmat,Join[#,{1}]][[1;;dim]]&/@unitcell,
##]&@@tabspec,(* specification of table, dim copies of loops from 0 to cover-1 *)
qdim]
];


CoveringTransformations[transf_,cover_]:=
Module[{i,qdim=Length[transf],tmat},
(* assuming that all matrices in transf commute... *)
tmat=Table[MatrixPower[transf[[i]],cover[[i]]],{i,qdim}]
];


(* this function was broken!!! *)
CoveringFrameworkEdges[edgedat_,cover_,periodic0_:False]:=
Module[{i,j,dim=Length[cover],ind1,ind2,p1,p2,edatExtend,m,numbonds=0,
bondlist=Table[Null,{Length[edgedat](Times@@cover)}],lenedge=Length[edgedat],
unitcellsize=Max[edgedat[[All,1]]],cellchange,tabspec,periodic,pdirs,cellchangenew},
periodic=If[BooleanQ[periodic0],Table[periodic0,{dim}],periodic0];
tabspec=Join[Table[{m[j],cover[[j]]},{j,dim}],{{i,lenedge}}];
Do[(* loop over edges in edgedat, (i.e. copy an edge i into all cells m,n) *)
edatExtend=Join[edgedat[[i,2,1;;Min[Length[edgedat[[i,2]]],dim]]],Table[0,{dim-Length[edgedat[[i,2]]]}]];
cellchange=Table[
(* ceiling -1 because we need right endpoint *)
Ceiling[(m[j]+edatExtend[[j]])/cover[[j]]-1],{j,dim}];
pdirs=Flatten[SparseArray[cellchange]["NonzeroPositions"]];
If[(And@@periodic[[pdirs]])||(cellchange==Table[0,{dim}]),
(* only add the bond if the periodic flag is set or it does not wrap*)
{p1,p2}=edgedat[[i,1]];
ind1=getatomindex2[Table[m[j],{j,dim}],p1,cover,unitcellsize];
ind2=getatomindex2[Table[Mod[m[j]+edatExtend[[j]],cover[[j]],1],{j,dim}],p2,cover,unitcellsize];
(* new cell change preserves ordering from original one but omits any directions 
that were specified False in periodic *)
cellchangenew=Flatten[Table[If[periodic[[j]],cellchange[[j]],{}],{j,dim}]];
numbonds++;
bondlist[[numbonds]]={{ind1,ind2},cellchangenew,edgedat[[i,3]]}
];
,##]&@@tabspec;
bondlist[[1;;numbonds]]
];


(* make a list of vertex positions in any dimension *)
(* with an arbitrary new basis *)
BCoveringFrameworkVerts[unitcell_,latt_,basis_,r_:0]:=
Module[{i,qdim=Length[latt],dim=Length[unitcell[[1]]],tabspec,m,
tA,tU,tD,tV,tDvec,pts,p,y},
tA=Transpose[basis];
(* tA has the basis as _columns_ *)
{tU,tD,tV}=smithNormalForm[tA];
tDvec=Table[tD[[j,j]],{j,qdim}];
tabspec=Table[{m[i],0,tDvec[[i]]-1},{i,qdim}];
(* pts is a list of points in the new unit cell *)
pts=Flatten[Table[
y=Table[m[i],{i,qdim}];
p=LinearSolve[tU.tA,y];
p=tA.Mod[p,1];
(* p is the list of integer points in the fundamental domain defined by "basis" *)
Table[
Sum[latt[[i]]*p[[i]],{i,qdim}]+If[r>0, RandomReal[{-r,r},dim],Table[0,{dim}]]
+unitcell[[i]],
{i,Length[unitcell]}]
,##]&@@tabspec,qdim]
];


(* connect up the points created by BCoveringFrameworkVerts *)
BCoveringFrameworkEdges[edgedat_,basis_,periodic0_:False]:=
Module[{i,j,dim=Length[basis],ind1,ind2,p1,p2,edatExtend,m,numbonds=0,
bondlist=Table[Null,{Length[edgedat](Abs[Det[basis]])}],lenedge=Length[edgedat],
unitcellsize=Max[edgedat[[All,1]]],cellchange,tabspec,
tA,tU,tD,tV,tDvec,pts,p,y,pp,ptemp,ptemp2,periodic,pdirs,cellchangenew},
periodic=If[BooleanQ[periodic0],Table[periodic0,{dim}],periodic0];
tA=Transpose[basis];
(* tA has the basis as _columns_ *)
{tU,tD,tV}=smithNormalForm[tA];
tDvec=Table[tD[[j,j]],{j,dim}];
tabspec=Table[{m[j],0,tDvec[[j]]-1},{j,dim}];

pts=Flatten[Table[y=Table[m[i],{i,dim}];
p=LinearSolve[tU.tA,y];
tA.Mod[p,1],##]&@@tabspec,dim-1];

Do[(* loop over edges in edgedat, (i.e. copy an edge i into all cells m,n) *)
{p1,p2}=edgedat[[i,1]];
edatExtend=Join[edgedat[[i,2,1;;Min[Length[edgedat[[i,2]]],dim]]],Table[0,{dim-Length[edgedat[[i,2]]]}]];

(* unit cell of p1 (index is k) *)
p=pts[[k]];
(* unit cell of p2 *)
pp=p+edatExtend;
ind1=unitcellsize(k-1)+p1;

(* need to convert pp into an index and a cellchange (relative to new basis) *)
(* first put in basis*) 
ptemp=LinearSolve[tA,pp];

(* to get index take mod, convert back, and then use Position *)
ptemp2=tA.Mod[ptemp,1];
ind2=unitcellsize(Position[pts,ptemp2][[1,1]]-1)+p2;

(* to get cellchange, measure the integer parts ? use floor now *)
cellchange=Floor[ptemp];
pdirs=Flatten[SparseArray[cellchange]["NonzeroPositions"]];
If[(And@@periodic[[pdirs]])||(cellchange==Table[0,{dim}]),

(* new cell change preserves ordering from original one but omits any directions 
that were specified False in periodic *)
cellchangenew=Flatten[Table[If[periodic[[j]],cellchange[[j]],{}],{j,dim}]];
numbonds++;
bondlist[[numbonds]]={{ind1,ind2},cellchangenew,edgedat[[i,3]]}
];
,{k,Length[pts]},{i,lenedge}];
bondlist[[1;;numbonds]]
];


(* slice; remove vertices, edges under a certain condition *)
(* if poscond is True when evaluated on vertex coordinates, KEEP the vertex;
if indexcond is False when evaluated on the vertex index, KEEP the vertex *)
(* return new edgedat and list of vertex indices *)
SliceOffVerts[pos_,edgedat_,poscond_,indexcond_:(False&)]:=
Module[{i,j,edgenew,keepers,numpartsold=Length[pos],throwers},
keepers=Flatten[Position[pos,_?(poscond),{1},Heads->False]];
keepers=Select[keepers,Not/@indexcond]; (* is this right ? *)
throwers=Complement[Table[i,{i,numpartsold}],keepers];
edgenew=Select[edgedat,Flatten[Intersection[#[[1]],throwers]]=={}&]; (* need to reindex ... *)
edgenew=Table[{edgenew[[j,1]]/.Table[keepers[[j]]->j,{j,Length[keepers]}],
edgenew[[j,2]],edgenew[[j,3]]},{j,Length[edgenew]}];
{edgenew,keepers}];


(* unwrap a periodic structure at the "seam", specified by the index seamdim *)
(* can use to get boundary vertices too for input into HarmonicExtension, etc *)
CutAtSeam[seamdim_,pos_,basis_,edgedat_]:=Module[{newedat,newpos,edatind,tempind,temp,j,pos1,pos2,
seamvec},
edatind=Flatten[Position[edgedat,_?(#[[2,seamdim]]!=0&),{1},Heads->False]];
(* want to put in new fake vertices at both ends of these edges *)
newedat=Join@@Table[If[MemberQ[edatind,j],
tempind=Position[edatind,j][[1,1]];
temp=edgedat[[j]];
(* indices of new vertices are 
Length[pos]+2tempind-1 (vertex that gets + seamvec.basis)
and
Length[pos]+2tempind (vertex that gets - seamvec.basis)
*)
{{{temp[[1,1]],Length[pos]+2tempind-1},{},temp[[3]]},
{{Length[pos]+2tempind,temp[[1,2]]},{},temp[[3]]}}
,
{edgedat[[j]]}
],{j,Length[edgedat]}];
newpos=Join@@Table[
temp=edgedat[[edatind[[j]]]];
pos1=pos[[temp[[1,1]]]];
pos2=pos[[temp[[1,2]]]];
seamvec=temp[[2]];
{pos2+seamvec.basis,pos1-seamvec.basis}
,{j,Length[edatind]}];
newpos=Join[pos,newpos];
{newpos,newedat}
]


glueedges[botE_,topE_,botdims_,botsize_,topdims_,topsize_,face_,cellglue_]:=
Module[{j,k,l,dim=Length[topdims],connectors,tabspec,ind,indbot,indtop,m},
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
];

glueverts[botV_,topV_,vec_]:=Join[botV,topV+Table[vec,{Length[topV]}]];


(* ::Section:: *)
(*Graphics functions*)


Label2DFramework[pos_,basis_,edat_,vpert_:{0,0},epert_:{0,0},vstyle_:{Black},estyle_:{Red}]:=
Module[{ecent,edatExtend,qdim=Length[basis]},
Graphics[Join[vstyle,Table[Text[j,pos[[j]]+vpert],{j,Length[pos]}],estyle,
Table[
edatExtend=Join[edat[[j,2,1;;Min[Length[edat[[j,2]]],qdim]]],Table[0,{qdim-Length[edat[[j,2]]]}]];
ecent=(pos[[edat[[j,1,1]]]]+pos[[edat[[j,1,2]]]]+edatExtend.basis)/2;
Text[j,ecent+epert],{j,Length[edat]}]]]]

Label3DFramework[pos_,basis_,edat_,vpert_:{0,0,0},epert_:{0,0,0},vstyle_:{Black},estyle_:{Red}]:=
Module[{ecent,edatExtend,qdim=Length[basis]},
Graphics3D[Join[vstyle,Table[Text[j,pos[[j]]+vpert],{j,Length[pos]}],estyle,
Table[
edatExtend=Join[edat[[j,2,1;;Min[Length[edat[[j,2]]],qdim]]],Table[0,{qdim-Length[edat[[j,2]]]}]];
ecent=(pos[[edat[[j,1,1]]]]+pos[[edat[[j,1,2]]]]+edatExtend.basis)/2;
Text[j,ecent+epert],{j,Length[edat]}]]]]


Draw2DFramework[p_,E_,pointstyle_:{},linestyle_:{}]:=Module[{i,j,e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]]
}]];


Draw2DFrameworkStress[p_,E_,stress_,mthick_:.01,colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{j,e=Length[E],nstr=mthick stress/Max[Abs[stress]]},
Graphics[{
Table[If[Abs[nstr[[j]]]>cutoff,{If[nstr[[j]]>0,colors[[1]],colors[[2]]],
AbsoluteThickness[Abs[nstr[[j]]]],Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}]},{}],
{j,e}]}]];


Draw2DFrameworkMode[p_,E_,nv_,pointstyle_:{},linestyle_:{},
col_:{Red},cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[2i-1;;2i]]]>cutoff,
Line[{p[[i]],p[[i]]+nv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}]];


Draw2DFrameworkModeArr[p_,E_,nv_,pointstyle_:{},linestyle_:{},
col_:{Red},cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[2i-1;;2i]]]>cutoff,
Arrow[{p[[i]],p[[i]]+nv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}]];


Draw2DFrameworkModeAmp[p_,E_,nv_,pointstyle_:{},linestyle_:{},
col_:{Red},cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[2i-1;;2i]]]>cutoff,
{PointSize->Norm[nv[[2i-1;;2i]]],Point[{p[[i]]}]},{}],{i,Length[p]}]]
}]];


DrawPeriodic2DFramework[p_,basis_,E_,copies_:{},pointstyle_:{},linestyle_:{}]:=
Module[{i,j,e=Length[E],dim=Length[basis],tabspec,m,cover,unitcell,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]]}
,##]&@@tabspec
]];


DrawTPeriodic2DFramework[p_,transformations_,E_,copies_:{},pointstyle_:{},
linestyle_:{}]:=
Module[{i,j,e=Length[E],dim=Length[transformations],tabspec,m,cover,
edatExtend,tmat,unitcell,pv,tmatp2},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
(*unitcell=Table[pv=tmat.Join[p[[i]],{1}];pv[[1;;2]],{i,Length[p]}];*)
unitcell=Dot[tmat,Join[#,{1}]][[1;;2]]&/@p;
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;2]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]]}
,##]&@@tabspec
]];


(* allow complex stresses(?), if so need qvec (a vector of z's) *)
DrawPeriodic2DFrameworkStress[p_,basis_,E_,stressinput_,copies_:{},mthick_:.01,
colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],stress,qvec,nstr,dim=Length[basis],tabspec,m,cover,
unitcell,edatExtend,realnstr},
(* dumb trick for backwards compatibility *)
If[(Length[stressinput]==2)&&(Length[stressinput[[1]]]==Length[E]),
qvec=stressinput[[2]];stress=stressinput[[1]];,
qvec=Table[1,{dim}];stress=stressinput;
];
nstr=mthick stress/Max[Abs[stress]];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnstr=Re[nstr Product[qvec[[i]]^m[i],{i,dim}]];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],
Table[0,{dim-Length[E[[j,2]]]}]];
{If[realnstr[[j]]>0,colors[[1]],colors[[2]]],
AbsoluteThickness[Abs[realnstr[[j]]]],
If[Abs[realnstr[[j]]]>cutoff,Line[{unitcell[[E[[j,1,1]]]],
unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{}]},{j,e}]
,##]&@@tabspec
]];


DrawTPeriodic2DFrameworkStress[p_,transformations_,E_,stressinput_,
copies_:{},mthick_:.01,colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],stress,qvec,nstr,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnstr},
(* dumb trick for backwards compatibility *)
If[(Length[stressinput]==2)&&(Length[stressinput[[1]]]==Length[E]),
qvec=stressinput[[2]];stress=stressinput[[1]];,
qvec=Table[1,{dim}];stress=stressinput;
];
nstr=mthick stress/Max[Abs[stress]];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;2]]&/@p;
realnstr=Re[nstr Product[qvec[[i]]^m[i],{i,dim}]];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
{If[realnstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[realnstr[[j]]]],
If[Abs[realnstr[[j]]]>cutoff,
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;2]]]}],{}]},{j,e}]
,##]&@@tabspec
]];


DrawPeriodic2DFrameworkMode[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],
tabspec,m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]]; 
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
Line[{unitcell[[i]],unitcell[[i]]+realnv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawPeriodic2DFrameworkModeArr[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]]; 
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
Arrow[{unitcell[[i]],unitcell[[i]]+realnv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic2DFrameworkMode[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;2]]&/@p;
realnv=Re[Flatten[Table[tmat[[;;2,;;2]].nv[[2i-1;;2i]],{i,Length[p]}]] Product[qvec[[i]]^m[i],{i,dim}]]; 
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;2]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
Line[{unitcell[[i]],unitcell[[i]]+realnv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic2DFrameworkModeArr[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;2]]&/@p;
realnv=Re[Flatten[Table[tmat[[;;2,;;2]].nv[[2i-1;;2i]],{i,Length[p]}]] Product[qvec[[i]]^m[i],{i,dim}]]; 
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;2]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
Arrow[{unitcell[[i]],unitcell[[i]]+realnv[[2i-1;;2i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawPeriodic2DFrameworkModeAmp[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]]; 
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
{PointSize->Norm[realnv[[2i-1;;2i]]],Point[{unitcell[[i]]}]},{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic2DFrameworkModeAmp[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==2Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;2]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]]; (* no need to rotate by tmat for just amplitude *)
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;2]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[2i-1;;2i]]]>cutoff,
{PointSize->Norm[realnv[[2i-1;;2i]]],Point[{unitcell[[i]]}]},{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


Draw3DFramework[p_,E_,pointstyle_:{},linestyle_:{}]:=Module[{i,j,e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]]
}]];


Draw3DFrameworkStress[p_,E_,stress_,mthick_:.01,colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{j,e=Length[E],nstr=mthick stress/Max[Abs[stress]]},
Graphics3D[{
Table[{
If[nstr[[j]]>0,colors[[1]],colors[[2]]],
AbsoluteThickness[Abs[nstr[[j]]]],
If[Abs[nstr[[j]]]>cutoff,Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{}]},{j,e}]
}]];


Draw3DFrameworkMode[p_,E_,nv_,pointstyle_:{},linestyle_:{},
col_:{Red},cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[3i-2;;3i]]]>cutoff,Line[{p[[i]],p[[i]]+nv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}]];


Draw3DFrameworkModeArr[p_,E_,nv_,pointstyle_:{},linestyle_:{},col_:{Red},
cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[Point[p[[i]]],{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[3i-2;;3i]]]>cutoff,Arrow[{p[[i]],p[[i]]+nv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}]];


Draw3DFrameworkModeAmp[p_,E_,nv_,pointstyle_:{},linestyle_:{},
col_:{Red},cutoff_:10^-5]:=Module[{i,j,e=Length[E]},
Graphics3D[{
Join[linestyle,Table[Line[{p[[E[[j,1,1]]]],p[[E[[j,1,2]]]]}],{j,e}]],
Join[pointstyle,Table[{Point[p[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[nv[[3i-2;;3i]]]>cutoff,
{PointSize->Norm[nv[[3i-2;;3i]]],Point[{p[[i]]}]},{}],{i,Length[p]}]]
}]];


DrawPeriodic3DFramework[p_,basis_,E_,copies_:{},pointstyle_:{},linestyle_:{}]:=
Module[{i,j,e=Length[E],dim=Length[basis],tabspec,m,cover,unitcell,edatExtend},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]]}
,##]&@@tabspec
]];


DrawTPeriodic3DFramework[p_,transformations_,E_,copies_:{},pointstyle_:{},linestyle_:{}]:=
Module[{i,j,e=Length[E],dim=Length[transformations],tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2},
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;3]]&/@p;
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;3]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]]}
,##]&@@tabspec
]];


(* allow complex stresses(?), if so need qvec *)
DrawPeriodic3DFrameworkStress[p_,basis_,E_,stressinput_,copies_:{},
mthick_:.01,colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],stress,qvec,nstr,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend,realnstr},
(* dumb trick for backwards compatibility *)
If[(Length[stressinput]==2)&&(Length[stressinput[[1]]]==Length[E]),
qvec=stressinput[[2]];stress=stressinput[[1]];,
qvec=Table[1,{dim}];stress=stressinput;
];
nstr=mthick stress/Max[Abs[stress]];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnstr=Re[nstr Product[qvec[[i]]^m[i],{i,dim}]];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
{If[realnstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[realnstr[[j]]]],
If[Abs[realnstr[[j]]]>cutoff,
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{}]},
{j,e}]
,##]&@@tabspec
]];


DrawTPeriodic3DFrameworkStress[p_,transformations_,E_,stressinput_,copies_:{},
mthick_:.01,colors_:{Purple,Orange},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],stress,qvec,nstr,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnstr},
(* dumb trick for backwards compatibility *)
If[(Length[stressinput]==2)&&(Length[stressinput[[1]]]==Length[E]),
qvec=stressinput[[2]];stress=stressinput[[1]];,
qvec=Table[1,{dim}];stress=stressinput;
];
nstr=mthick stress/Max[Abs[stress]];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;3]]&/@p;
realnstr=Re[nstr Product[qvec[[i]]^m[i],{i,dim}]];
Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
{If[realnstr[[j]]>0,colors[[1]],colors[[2]]],AbsoluteThickness[Abs[realnstr[[j]]]],
If[Abs[realnstr[[j]]]>cutoff,
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;3]]]}],{}]},{j,e}]
,##]&@@tabspec
]];


DrawPeriodic3DFrameworkMode[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
Line[{unitcell[[i]],unitcell[[i]]+realnv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawPeriodic3DFrameworkModeArr[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
Arrow[{unitcell[[i]],unitcell[[i]]+realnv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawPeriodic3DFrameworkModeArrTube[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
Arrow[Tube[{unitcell[[i]],unitcell[[i]]+realnv[[3i-2;;3i]]}]],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic3DFrameworkMode[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;3]]&/@p;
realnv=Re[Flatten[Table[tmat[[;;3,;;3]].nv[[3i-2;;3i]],{i,Length[p]}]] Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;3]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
Line[{unitcell[[i]],unitcell[[i]]+realnv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic3DFrameworkModeArr[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],
tabspec,m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;3]]&/@p;
realnv=Re[Flatten[Table[tmat[[;;3,;;3]].nv[[3i-2;;3i]],{i,Length[p]}]] Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;3]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
Arrow[{unitcell[[i]],unitcell[[i]]+realnv[[3i-2;;3i]]}],{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawPeriodic3DFrameworkModeAmp[p_,basis_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,realnv,dim=Length[basis],tabspec,
m,cover,unitcell,edatExtend},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
unitcell=Plus[#,Sum[m[i]*basis[[i]],{i,dim}]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]];
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],unitcell[[E[[j,1,2]]]]+edatExtend.basis}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
{PointSize->Norm[realnv[[3i-2;;3i]]],Point[{unitcell[[i]]}]},{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


DrawTPeriodic3DFrameworkModeAmp[p_,transformations_,E_,nvinput_,copies_:{},
pointstyle_:{},linestyle_:{},col_:{Red},cutoff_:10^-5]:=
Module[{i,j,e=Length[E],nv,qvec,dim=Length[transformations],tabspec,
m,cover,edatExtend,tmat,unitcell,pv,tmatp2,realnv},
(* dumb trick for backwards compatibility *)
If[(Length[nvinput]==2)&&(Length[nvinput[[1]]]==3Length[p]),
qvec=nvinput[[2]];nv=nvinput[[1]];,
qvec=Table[1,{dim}];nv=nvinput;
];
cover=If[Length[copies]!=dim,Table[1,{dim}],copies];
tabspec=Table[{m[i],0,cover[[i]]-1},{i,dim}];
Graphics3D[
Table[
tmat=Dot@@Table[MatrixPower[transformations[[i]],m[i]],{i,dim}]; (* maybe could memoize *)
(* shifted unit cell positions *)
unitcell=Dot[tmat,Join[#,{1}]][[1;;3]]&/@p;
realnv=Re[nv Product[qvec[[i]]^m[i],{i,dim}]]; (* no need to rotate by tmat for just amplitude *)
{Join[linestyle,Table[
edatExtend=Join[E[[j,2,1;;Min[Length[E[[j,2]]],dim]]],Table[0,{dim-Length[E[[j,2]]]}]];
Line[{unitcell[[E[[j,1,1]]]],If[edatExtend==Table[0,{dim}],unitcell[[E[[j,1,2]]]],
(* apply appropriate transformation again to get line to second particle *)
tmatp2=Dot@@Table[MatrixPower[transformations[[i]],edatExtend[[i]]],{i,dim}]; (* maybe could memoize *)
pv=tmatp2.Join[unitcell[[E[[j,1,2]]]],{1}];
pv[[1;;3]]]}],{j,e}]],
Join[pointstyle,Table[{Point[unitcell[[i]]]},{i,Length[p]}]],
Join[col,Table[If[Norm[realnv[[3i-2;;3i]]]>cutoff,
{PointSize->Norm[realnv[[3i-2;;3i]]],Point[{unitcell[[i]]}]},{}],{i,Length[p]}]]
}
,##]&@@tabspec
]];


FirstBZ[basis_,xwind_,ywind_,opts_:{},maxcheck_:2,shift_:{0,0}]:=Module[{qx,qy,rec,reciplist,reciprocbasis},
reciprocbasis={2\[Pi] {{0,1},{-1,0}}.basis[[2]]/(basis[[1]].({{0,1},{-1,0}}.basis[[2]])),
2\[Pi] {{0,-1},{1,0}}.basis[[1]]/(basis[[2]].({{0,-1},{1,0}}.basis[[1]]))};
reciplist=Union[Flatten[Table[If[{j,k}!={0,0},j reciprocbasis[[1]]+k reciprocbasis[[2]], reciprocbasis[[1]]+reciprocbasis[[2]]],
{j,-maxcheck,maxcheck},{k,-maxcheck,maxcheck}],1]];(*Print[reciplist];*)
RegionPlot[
Norm[{qx,qy}-shift]<Min[Table[Norm[{qx,qy}-shift-reciplist[[j]]],{j,Length[reciplist]}]],
{qx,xwind[[1]],xwind[[2]]},{qy,ywind[[1]],ywind[[2]]},opts]]


BandPlot[{zx_,zy_},poly_,basis_:{{1,0},{0,1}},xwind_:{-\[Pi],\[Pi]},ywind_:{-\[Pi],\[Pi]},opts_:{MaxRecursion->Automatic}]:=
Module[{qx,qy,b,rec},
ContourPlot[
Evaluate[rec={qx,qy}.Transpose[basis];(poly/.{zx->Exp[I rec[[1]]],zy->Exp[I rec[[2]]]})],
{qx,xwind[[1]],xwind[[2]]},{qy,ywind[[1]],ywind[[2]]},opts]];

BandPlot3D[{zx_,zy_},poly_,basis_:{{1,0},{0,1}},xwind_:{-\[Pi],\[Pi]},ywind_:{-\[Pi],\[Pi]},opts_:{MaxRecursion->Automatic}]:=
Module[{qx,qy,b,rec},
Plot3D[Evaluate[rec={qx,qy}.Transpose[basis];(poly/.{zx->Exp[I rec[[1]]],zy->Exp[I rec[[2]]]})],
{qx,xwind[[1]],xwind[[2]]},{qy,ywind[[1]],ywind[[2]]},opts]];

(* function that plots function(s) of q along a piecewise linear path in q-space *)
BandPathPlot[z_,poly_,path_,opts_:{MaxRecursion->Automatic}]:=
Module[{interpdat,j,rec,func,prev,f},
interpdat=Table[{prev=If[j==1,0,prev+Norm[path[[j]]-path[[j-1]]]],
path[[j]]},{j,Length[path]}];
func=Interpolation[interpdat,#,InterpolationOrder->1]&;
Plot[
f=func[t];poly/.Table[z[[j]]->Exp[I f[[j]]],{j,Length[z]}],{t,0,prev},opts]];


Draw2DUnitCellShapeChange[basis_,nv_,showorig_:True]:=Graphics[
{If[showorig,{Gray,Dashed,Arrow[{{0,0},basis[[1]]}],
Arrow[{{0,0},basis[[2]]}]},{}],GrayLevel[0.3],Dashing[{}],
Arrow[{{0,0},basis[[1]]+nv[[-4;;-3]]}],Arrow[{{0,0},basis[[2]]+nv[[-2;;-1]]}]}
]

Draw2DUnitCellShapeChangeArr[basis_,nv_]:=Graphics[
{{Gray,Dashed,Arrow[{{0,0},basis[[1]]}],
Arrow[{{0,0},basis[[2]]}]},GrayLevel[0.3],Dashing[{}],
Arrow[{basis[[1]],basis[[1]]+nv[[-4;;-3]]}],Arrow[{basis[[2]],basis[[2]]+nv[[-2;;-1]]}]}
]


(* ::Section:: *)
(*End*)


End[];
EndPackage[]
