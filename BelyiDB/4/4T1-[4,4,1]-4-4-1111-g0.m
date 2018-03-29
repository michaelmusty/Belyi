s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "4T1-[4,4,1]-4-4-1111-g0";
s`BelyiDBFilename := "4T1-[4,4,1]-4-4-1111-g0.m";
s`BelyiDBDegree := 4;
s`BelyiDBOrders := \[ 4, 4, 1 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 > |
[ 2, 3, 4, 1 ],
[ 4, 1, 2, 3 ],
[ 1, 2, 3, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<4 |  
\[ 2, 3, 4, 1 ],
\[ 4, 1, 2, 3 ],
\[ 1, 2, 3, 4 ]:
 Order := 4 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<4 |  
\[ 2, 3, 4, 1 ],
\[ 4, 1, 2, 3 ],
\[ 1, 2, 3, 4 ]:
 Order := 4 >) |
[ PermutationGroup<4 |  
\[ 2, 3, 4, 1 ],
\[ 4, 1, 2, 3 ],
\[ 1, 2, 3, 4 ]:
 Order := 4 > |
[ 2, 3, 4, 1 ],
[ 4, 1, 2, 3 ],
[ 1, 2, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 >) |
[ PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 > |
[ 2, 3, 4, 1 ],
[ 4, 1, 2, 3 ],
[ 1, 2, 3, 4 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 >)) |
[ PowerSequence(PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 >) |
[ PermutationGroup<4 |  
\[ 2, 3, 4, 1 ]:
 Order := 4 > |
[ 2, 3, 4, 1 ],
[ 4, 1, 2, 3 ],
[ 1, 2, 3, 4 ]
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
phi1 := KX1!(-1/(x^4 - 1));
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
