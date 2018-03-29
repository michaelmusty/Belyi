s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,20,3]-6111-54-33111-g0";
s`BelyiDBFilename := "9T34-[6,20,3]-6111-54-33111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 20, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 7, 8, 6, 3, 4, 5, 2, 9, 1 ],
[ 3, 9, 7, 4, 5, 6, 1, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 7, 2, 9, 4, 5, 8, 1, 6 ],
[ 9, 8, 3, 1, 5, 6, 2, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
\[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 8, 7, 2, 3, 4, 1, 5, 9, 6 ],
[ 9, 6, 3, 4, 5, 7, 2, 1, 8 ]
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
[ 6, 8, 7, 3, 4, 2, 5, 9, 1 ],
[ 1, 9, 6, 4, 5, 7, 3, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 7, 8, 6, 3, 4, 5, 2, 9, 1 ],
[ 3, 9, 7, 4, 5, 6, 1, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 3, 7, 2, 9, 4, 5, 8, 1, 6 ],
[ 9, 8, 3, 1, 5, 6, 2, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 8, 7, 2, 3, 4, 1, 5, 9, 6 ],
[ 9, 6, 3, 4, 5, 7, 2, 1, 8 ]
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
