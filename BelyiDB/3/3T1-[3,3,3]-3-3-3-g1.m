s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "3T1-[3,3,3]-3-3-3-g1";
s`BelyiDBFilename := "3T1-[3,3,3]-3-3-3-g1.m";
s`BelyiDBDegree := 3;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 > |
[ 2, 3, 1 ],
[ 2, 3, 1 ],
[ 2, 3, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<3 |  
\[ 2, 3, 1 ],
\[ 2, 3, 1 ],
\[ 2, 3, 1 ]:
 Order := 3 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<3 |  
\[ 2, 3, 1 ],
\[ 2, 3, 1 ],
\[ 2, 3, 1 ]:
 Order := 3 >) |
[ PermutationGroup<3 |  
\[ 2, 3, 1 ],
\[ 2, 3, 1 ],
\[ 2, 3, 1 ]:
 Order := 3 > |
[ 2, 3, 1 ],
[ 2, 3, 1 ],
[ 2, 3, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 >) |
[ PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 > |
[ 2, 3, 1 ],
[ 2, 3, 1 ],
[ 2, 3, 1 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 >)) |
[ PowerSequence(PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 >) |
[ PermutationGroup<3 |  
\[ 2, 3, 1 ]:
 Order := 3 > |
[ 2, 3, 1 ],
[ 2, 3, 1 ],
[ 2, 3, 1 ]
]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := NumberField(Polynomial([RationalField() | 1, 1, 1]));
place1 := InfinitePlaces(K1)[1];
conj1 := false;
CC<I> := ComplexField(20);
z1 := 0.00000000000000000000p20;
base_field_data_1 := [* K1, place1, conj1, z1 *];
Append(~base_field_data, base_field_data_1);
s`BelyiDBBaseFieldData := base_field_data;

/*
Belyi Maps
*/

curves := [* *];
maps := [* *];
K := K1;
aInvs1 := [0,0,0,0,1];
E1 := EllipticCurve(aInvs1);
X1 := BaseChange(E1, K1);
KX1<x,y> := FunctionField(X1);
phi1 := KX1!(-1/2*y + 1/2);
Append(~curves, X1);
Append(~maps, phi1);
s`BelyiDBBelyiCurves := curves;
s`BelyiDBBelyiMaps := maps;

/*
Exact Data
*/


/*
Numerical Data
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
