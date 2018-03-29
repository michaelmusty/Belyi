s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "6T4-[3,3,3]-33-33-33-g1";
s`BelyiDBFilename := "6T4-[3,3,3]-33-33-33-g1.m";
s`BelyiDBDegree := 6;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 > |
[ 3, 4, 5, 6, 1, 2 ],
[ 6, 4, 2, 3, 1, 5 ],
[ 6, 1, 5, 3, 4, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<6 |  
\[ 4, 5, 6, 1, 2, 3 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<6 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<6 |  
\[ 3, 4, 5, 6, 1, 2 ],
\[ 6, 4, 2, 3, 1, 5 ],
\[ 6, 1, 5, 3, 4, 2 ]:
 Order := 12 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 3, 4, 5, 6, 1, 2 ],
\[ 6, 4, 2, 3, 1, 5 ],
\[ 6, 1, 5, 3, 4, 2 ]:
 Order := 12 >) |
[ PermutationGroup<6 |  
\[ 3, 4, 5, 6, 1, 2 ],
\[ 6, 4, 2, 3, 1, 5 ],
\[ 6, 1, 5, 3, 4, 2 ]:
 Order := 12 > |
[ 3, 4, 5, 6, 1, 2 ],
[ 6, 4, 2, 3, 1, 5 ],
[ 6, 1, 5, 3, 4, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 >) |
[ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 > |
[ 3, 4, 5, 6, 1, 2 ],
[ 6, 4, 2, 3, 1, 5 ],
[ 6, 1, 5, 3, 4, 2 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 >)) |
[ PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 >) |
[ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ]:
 Order := 12 > |
[ 3, 4, 5, 6, 1, 2 ],
[ 6, 4, 2, 3, 1, 5 ],
[ 6, 1, 5, 3, 4, 2 ]
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
aInvs1 := [0,0,0,-15,22];
E1 := EllipticCurve(aInvs1);
X1 := BaseChange(E1, K1);
KX1<x,y> := FunctionField(X1);
phi1 := KX1!((-1/16*x^2 + 1/4*x - 7/16)/(x^2 - 4*x + 4)*y + 1/2);
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
