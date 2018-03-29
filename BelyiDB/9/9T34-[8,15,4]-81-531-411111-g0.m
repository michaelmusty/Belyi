s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,15,4]-81-531-411111-g0";
s`BelyiDBFilename := "9T34-[8,15,4]-81-531-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 15, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 3, 1, 2, 4, 9, 5, 6, 7, 8 ],
[ 9, 2, 3, 1, 4, 6, 7, 8, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 9, 2, 8, 4, 5, 6, 7, 3 ],
[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
\[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
\[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 4, 2, 3, 9, 5, 6, 7, 8 ],
[ 9, 1, 3, 4, 2, 6, 7, 8, 5 ]
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
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 6, 2, 3, 4, 5, 9, 7, 8 ],
[ 9, 1, 3, 4, 5, 6, 2, 8, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 9, 2, 3, 4, 8, 6, 7, 5 ],
[ 6, 1, 3, 4, 5, 9, 7, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 9, 2, 8, 4, 5, 6, 7, 3 ],
[ 4, 1, 3, 9, 5, 6, 7, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 4, 2, 3, 9, 5, 6, 7, 8 ],
[ 9, 1, 3, 4, 2, 6, 7, 8, 5 ]
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
