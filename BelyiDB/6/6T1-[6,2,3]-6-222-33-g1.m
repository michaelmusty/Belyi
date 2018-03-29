s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "6T1-[6,2,3]-6-222-33-g1";
s`BelyiDBFilename := "6T1-[6,2,3]-6-222-33-g1.m";
s`BelyiDBDegree := 6;
s`BelyiDBOrders := \[ 6, 2, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 > |
[ 2, 3, 4, 5, 6, 1 ],
[ 4, 5, 6, 1, 2, 3 ],
[ 3, 4, 5, 6, 1, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 >;
s`BelyiDBMonodromyGroup := PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ],
\[ 4, 5, 6, 1, 2, 3 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 6 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ],
\[ 4, 5, 6, 1, 2, 3 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 6 >) |
[ PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ],
\[ 4, 5, 6, 1, 2, 3 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 6 > |
[ 6, 1, 2, 3, 4, 5 ],
[ 4, 5, 6, 1, 2, 3 ],
[ 5, 6, 1, 2, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 >) |
[ PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 > |
[ 2, 3, 4, 5, 6, 1 ],
[ 4, 5, 6, 1, 2, 3 ],
[ 3, 4, 5, 6, 1, 2 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 >)) |
[ PowerSequence(PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 >) |
[ PermutationGroup<6 |  
\[ 2, 3, 4, 5, 6, 1 ]:
 Order := 6 > |
[ 2, 3, 4, 5, 6, 1 ],
[ 4, 5, 6, 1, 2, 3 ],
[ 3, 4, 5, 6, 1, 2 ]
]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := RationalsAsNumberField();
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
aInvs1 := [0,0,0,0,-1];
E1 := EllipticCurve(aInvs1);
X1 := BaseChange(E1, K1);
KX1<x,y> := FunctionField(X1);
phi1 := KX1!(1/x^3);
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
