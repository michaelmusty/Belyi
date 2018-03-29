s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,3,6]-81-3111111-63-g0";
s`BelyiDBFilename := "9T34-[8,3,6]-81-3111111-63-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 7, 2, 3, 4, 5, 6, 9, 8, 1 ],
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 4, 2, 3, 9, 5, 6, 7, 8, 1 ],
[ 2, 3, 1, 5, 6, 7, 8, 9, 4 ]
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
[ 5, 2, 9, 3, 4, 1, 6, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ],
[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 8, 2, 1, 4, 5, 6, 7, 9 ],
[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 3, 9, 5, 6, 7, 8, 1, 2 ]
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
