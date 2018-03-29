s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "6T7-[4,3,2]-42-33-2211-g0";
s`BelyiDBFilename := "6T7-[4,3,2]-42-33-2211-g0.m";
s`BelyiDBDegree := 6;
s`BelyiDBOrders := \[ 4, 3, 2 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 > |
[ 3, 5, 4, 6, 2, 1 ],
[ 2, 3, 1, 5, 6, 4 ],
[ 5, 4, 3, 2, 1, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<6 |  
\[ 4, 5, 6, 1, 2, 3 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<6 |  
\[ 4, 5, 6, 1, 2, 3 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<6 |  
\[ 3, 5, 4, 6, 2, 1 ],
\[ 2, 3, 1, 5, 6, 4 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 3, 5, 4, 6, 2, 1 ],
\[ 2, 3, 1, 5, 6, 4 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 >) |
[ PermutationGroup<6 |  
\[ 3, 5, 4, 6, 2, 1 ],
\[ 2, 3, 1, 5, 6, 4 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 > |
[ 3, 5, 4, 6, 2, 1 ],
[ 2, 3, 1, 5, 6, 4 ],
[ 5, 4, 3, 2, 1, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 >) |
[ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 > |
[ 3, 5, 4, 6, 2, 1 ],
[ 2, 3, 1, 5, 6, 4 ],
[ 5, 4, 3, 2, 1, 6 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 >)) |
[ PowerSequence(PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 >) |
[ PermutationGroup<6 |  
\[ 4, 5, 3, 1, 2, 6 ],
\[ 3, 4, 5, 6, 1, 2 ],
\[ 5, 4, 3, 2, 1, 6 ]:
 Order := 24 > |
[ 3, 5, 4, 6, 2, 1 ],
[ 2, 3, 1, 5, 6, 4 ],
[ 5, 4, 3, 2, 1, 6 ]
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
phi1 := KX1!(-108*x^2/(x^6 + 12*x^4 - 60*x^2 + 64));
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
