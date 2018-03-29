s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,4]-6111-6111-441-g0";
s`BelyiDBFilename := "9T34-[6,6,4]-6111-6111-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 7, 2, 4, 5, 6, 8, 9, 1 ],
[ 6, 9, 3, 1, 4, 5, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 7, 3, 5, 6, 8, 1, 4 ],
[ 6, 8, 2, 4, 9, 5, 3, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
\[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 1, 8, 3, 4, 7, 5, 2, 9, 6 ],
[ 9, 1, 7, 3, 4, 6, 5, 2, 8 ]
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
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 3, 4, 5, 2, 8, 9, 1 ],
[ 1, 9, 6, 3, 4, 5, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 7, 2, 4, 5, 6, 8, 9, 1 ],
[ 6, 9, 3, 1, 4, 5, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 7, 3, 5, 6, 8, 1, 4 ],
[ 6, 8, 2, 4, 9, 5, 3, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 1, 8, 3, 4, 7, 5, 2, 9, 6 ],
[ 9, 1, 7, 3, 4, 6, 5, 2, 8 ]
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
