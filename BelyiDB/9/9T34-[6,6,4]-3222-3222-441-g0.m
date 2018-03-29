s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,4]-3222-3222-441-g0";
s`BelyiDBFilename := "9T34-[6,6,4]-3222-3222-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 5, 4, 3, 2, 8, 9, 1, 7 ],
[ 7, 8, 5, 9, 3, 2, 1, 6, 4 ],
[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 5, 4, 3, 2, 8, 9, 1, 7 ],
\[ 7, 8, 5, 9, 3, 2, 1, 6, 4 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 5, 4, 3, 2, 8, 9, 1, 7 ],
\[ 7, 8, 5, 9, 3, 2, 1, 6, 4 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 5, 4, 3, 2, 8, 9, 1, 7 ],
\[ 7, 8, 5, 9, 3, 2, 1, 6, 4 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 362880 > |
[ 8, 7, 6, 5, 4, 3, 9, 1, 2 ],
[ 5, 8, 9, 6, 1, 4, 3, 2, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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
[ 6, 5, 4, 3, 2, 8, 9, 1, 7 ],
[ 7, 8, 5, 9, 3, 2, 1, 6, 4 ],
[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]
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
