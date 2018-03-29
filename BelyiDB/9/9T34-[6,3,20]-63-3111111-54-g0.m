s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,3,20]-63-3111111-54-g0";
s`BelyiDBFilename := "9T34-[6,3,20]-63-3111111-54-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 20 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 9, 7, 8 ],
[ 1, 8, 2, 4, 5, 6, 7, 3, 9 ],
[ 3, 8, 4, 5, 6, 1, 2, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 9, 7, 8 ],
[ 1, 6, 3, 4, 5, 8, 7, 2, 9 ],
[ 8, 3, 4, 5, 2, 1, 6, 9, 7 ]
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
[ 2, 9, 5, 3, 4, 1, 6, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
[ 6, 3, 4, 5, 2, 7, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 9, 3, 4, 5, 2, 7, 1 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
[ 9, 7, 4, 5, 6, 3, 8, 1, 2 ]
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
