s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,3,4]-81-333-411111-g0";
s`BelyiDBFilename := "9T34-[8,3,4]-81-333-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 2, 9, 6, 1, 5, 4, 7, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 2, 9, 6, 1, 5, 4, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 2, 9, 6, 1, 5, 4, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 2, 9, 6, 1, 5, 4, 7, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 7, 3, 4, 2, 6, 9, 8, 1, 5 ],
[ 4, 2, 3, 9, 5, 1, 7, 8, 6 ]
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
[ 3, 2, 9, 6, 1, 5, 4, 7, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]
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
