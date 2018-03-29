s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "7T4-[6,3,2]-61-331-2221-g0";
s`BelyiDBFilename := "7T4-[6,3,2]-61-331-2221-g0.m";
s`BelyiDBDegree := 7;
s`BelyiDBOrders := \[ 6, 3, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7 ]:
 Order := 42 > |
[ 6, 4, 2, 7, 5, 3, 1 ],
[ 1, 5, 2, 6, 3, 7, 4 ],
[ 6, 5, 4, 3, 2, 1, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<7 |  
\[ 6, 4, 2, 7, 5, 3, 1 ],
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 6, 5, 4, 3, 2, 1, 7 ]:
 Order := 42 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 6, 4, 2, 7, 5, 3, 1 ],
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 6, 5, 4, 3, 2, 1, 7 ]:
 Order := 42 >) |
[ PermutationGroup<7 |  
\[ 6, 4, 2, 7, 5, 3, 1 ],
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 6, 5, 4, 3, 2, 1, 7 ]:
 Order := 42 > |
[ 6, 4, 2, 7, 5, 3, 1 ],
[ 5, 2, 6, 3, 7, 4, 1 ],
[ 5, 4, 3, 2, 1, 7, 6 ]
],
[ PermutationGroup<7 |  
\[ 6, 4, 2, 7, 5, 3, 1 ],
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 6, 5, 4, 3, 2, 1, 7 ]:
 Order := 42 > |
[ 7, 3, 6, 2, 5, 1, 4 ],
[ 7, 2, 4, 6, 1, 3, 5 ],
[ 4, 3, 2, 1, 7, 6, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7 ]:
 Order := 42 >) |
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7 ]:
 Order := 42 > |
[ 6, 4, 2, 7, 5, 3, 1 ],
[ 1, 5, 2, 6, 3, 7, 4 ],
[ 6, 5, 4, 3, 2, 1, 7 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7 ]:
 Order := 42 > |
[ 7, 3, 6, 2, 5, 1, 4 ],
[ 3, 5, 7, 2, 4, 6, 1 ],
[ 6, 5, 4, 3, 2, 1, 7 ]
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
K2<nu2> := NumberField(Polynomial([RationalField() | 1, 1, 1]));
place2 := InfinitePlaces(K2)[1];
conj2 := true;
CC<I> := ComplexField(20);
z2 := 0.00000000000000000000p20;
base_field_data_2 := [* K2, place2, conj2, z2 *];
Append(~base_field_data, base_field_data_2);
s`BelyiDBBaseFieldData := base_field_data;

/*
Belyi Maps
*/

curves := [* *];
maps := [* *];
K := K1;
X1 := Curve(ProjectiveSpace(PolynomialRing(K1, 2)));
KX1<x> := FunctionField(X1);
phi1 := KX1!((117649*x^6 + (-100438632*nu1 + 305349576)*x^5 + (-252961868880*nu1 + 294486299520)*x^4 + (-249757507560960*nu1 + 121857998769920)*x^3 + (-120685154700015360*nu1 + 12881522436921600)*x^2 + (-28483831934859184128*nu1 - 4639837950983811072)*x - 2618991931111749550080*nu1 - 1009983950540445888512)/(x^7 + (-1008*nu1 + 69685)*x^6 + (-59964408*nu1 + 1089111576)*x^5 + (-785424393936*nu1 - 4332819236032)*x^4 + (2109076286317056*nu1 + 4513307712639488)*x^3 + (-1306377131454597888*nu1 - 1156001180632763136)*x^2 + (114150262482422175744*nu1 + 67793952422013927424)*x - 2618991931111749550080*nu1 - 1009983950540445888512));
Append(~curves, X1);
Append(~maps, phi1);
K := K2;
X2 := Curve(ProjectiveSpace(PolynomialRing(K2, 2)));
KX2<x> := FunctionField(X2);
phi2 := KX2!((117649*x^6 + (-100438632*nu2 + 305349576)*x^5 + (-252961868880*nu2 + 294486299520)*x^4 + (-249757507560960*nu2 + 121857998769920)*x^3 + (-120685154700015360*nu2 + 12881522436921600)*x^2 + (-28483831934859184128*nu2 - 4639837950983811072)*x - 2618991931111749550080*nu2 - 1009983950540445888512)/(x^7 + (-1008*nu2 + 69685)*x^6 + (-59964408*nu2 + 1089111576)*x^5 + (-785424393936*nu2 - 4332819236032)*x^4 + (2109076286317056*nu2 + 4513307712639488)*x^3 + (-1306377131454597888*nu2 - 1156001180632763136)*x^2 + (114150262482422175744*nu2 + 67793952422013927424)*x - 2618991931111749550080*nu2 - 1009983950540445888512));
Append(~curves, X2);
Append(~maps, phi2);
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
