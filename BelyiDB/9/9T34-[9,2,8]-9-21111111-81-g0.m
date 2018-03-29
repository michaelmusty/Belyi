s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[9,2,8]-9-21111111-81-g0";
s`BelyiDBFilename := "9T34-[9,2,8]-9-21111111-81-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 2, 8 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 9, 2, 3, 4, 5, 6, 7, 1 ],
[ 1, 9, 3, 4, 5, 6, 7, 8, 2 ],
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 9, 2, 3, 4, 5, 6, 7, 1 ],
\[ 1, 9, 3, 4, 5, 6, 7, 8, 2 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 9, 2, 3, 4, 5, 6, 7, 1 ],
\[ 1, 9, 3, 4, 5, 6, 7, 8, 2 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 8, 9, 2, 3, 4, 5, 6, 7, 1 ],
\[ 1, 9, 3, 4, 5, 6, 7, 8, 2 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ]:
 Order := 362880 > |
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 1, 3, 2, 4, 5, 6, 7, 8, 9 ],
[ 3, 2, 4, 5, 6, 7, 8, 9, 1 ]
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
[ 8, 9, 2, 3, 4, 5, 6, 7, 1 ],
[ 1, 9, 3, 4, 5, 6, 7, 8, 2 ],
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ]
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
