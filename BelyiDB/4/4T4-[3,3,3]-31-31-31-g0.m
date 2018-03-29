s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "4T4-[3,3,3]-31-31-31-g0";
s`BelyiDBFilename := "4T4-[3,3,3]-31-31-31-g0.m";
s`BelyiDBDegree := 4;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 > |
[ 2, 3, 1, 4 ],
[ 3, 2, 4, 1 ],
[ 1, 4, 2, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<4 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<4 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<4 |  
\[ 2, 3, 1, 4 ],
\[ 3, 2, 4, 1 ],
\[ 1, 4, 2, 3 ]:
 Order := 12 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<4 |  
\[ 2, 3, 1, 4 ],
\[ 3, 2, 4, 1 ],
\[ 1, 4, 2, 3 ]:
 Order := 12 >) |
[ PermutationGroup<4 |  
\[ 2, 3, 1, 4 ],
\[ 3, 2, 4, 1 ],
\[ 1, 4, 2, 3 ]:
 Order := 12 > |
[ 2, 3, 1, 4 ],
[ 3, 2, 4, 1 ],
[ 1, 4, 2, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 >) |
[ PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 > |
[ 2, 3, 1, 4 ],
[ 3, 2, 4, 1 ],
[ 1, 4, 2, 3 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 >)) |
[ PowerSequence(PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 >) |
[ PermutationGroup<4 |  
\[ 3, 2, 4, 1 ],
\[ 1, 3, 4, 2 ]:
 Order := 12 > |
[ 2, 3, 1, 4 ],
[ 3, 2, 4, 1 ],
[ 1, 4, 2, 3 ]
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
X1 := Curve(ProjectiveSpace(PolynomialRing(K1, 2)));
KX1<x> := FunctionField(X1);
phi1 := KX1!((-4*x^4 + 4*x^3)/(x - 1/4));
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
