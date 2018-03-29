s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,6]-621-3222-3222-g0";
s`BelyiDBFilename := "9T34-[6,6,6]-621-3222-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
\[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
\[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
\[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ],
[ 4, 3, 9, 1, 7, 8, 5, 6, 2 ],
[ 8, 4, 9, 2, 1, 7, 6, 5, 3 ]
],
[ PermutationGroup<9 |  
\[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
\[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ],
[ 3, 9, 1, 6, 8, 7, 4, 5, 2 ],
[ 4, 3, 9, 1, 7, 8, 5, 6, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 2, 1, 8, 3, 9, 5, 7, 6 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
[ 2, 1, 4, 3, 6, 8, 9, 5, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 8, 9, 7, 3, 6, 5, 2, 1 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ],
[ 8, 9, 4, 3, 6, 7, 5, 1, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
