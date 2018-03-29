s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,3,6]-81-33111-6111-g0";
s`BelyiDBFilename := "9T34-[8,3,6]-81-33111-6111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 9, 4, 5, 3, 6, 7, 8, 1 ],
[ 1, 5, 3, 4, 6, 7, 8, 9, 2 ]
],
[ PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 9, 3, 5, 6, 4, 7, 8, 1 ],
[ 1, 3, 6, 4, 5, 7, 8, 9, 2 ]
],
[ PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 9, 2, 3, 4, 6, 7, 5, 1, 8 ],
[ 2, 3, 4, 7, 5, 6, 9, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
\[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 9, 3, 4, 6, 7, 5, 8, 1 ],
[ 1, 3, 4, 7, 5, 6, 8, 9, 2 ]
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
[ 6, 8, 3, 7, 4, 5, 2, 9, 1 ],
[ 1, 9, 7, 3, 5, 6, 4, 2, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 2, 4, 7, 5, 3, 9, 1 ],
[ 1, 9, 3, 7, 4, 6, 5, 2, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 7, 2, 3, 4, 6, 8, 1, 5 ],
[ 6, 8, 3, 4, 5, 9, 2, 7, 1 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 2, 3, 5, 7, 4, 9, 1 ],
[ 1, 9, 3, 4, 7, 5, 6, 2, 8 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
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
