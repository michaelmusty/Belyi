s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,2,6]-81-22221-6111-g0";
s`BelyiDBFilename := "9T34-[8,2,6]-81-22221-6111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 2, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
[ 3, 2, 5, 4, 7, 6, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 9, 2, 4, 3, 6, 5, 8, 7, 1 ],
[ 2, 4, 3, 6, 5, 8, 7, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 9, 3, 2, 4, 6, 5, 8, 7, 1 ],
[ 3, 2, 4, 6, 5, 8, 7, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
\[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 1, 9, 5, 4, 7, 6, 8, 3 ],
[ 1, 9, 5, 4, 7, 6, 8, 2, 3 ]
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
[ 9, 8, 7, 4, 3, 5, 2, 1, 6 ],
[ 9, 8, 7, 5, 4, 6, 3, 2, 1 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 7, 3, 5, 4, 2, 1, 6 ],
[ 9, 8, 7, 4, 6, 5, 3, 2, 1 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 2, 7, 5, 4, 3, 1, 6 ],
[ 9, 8, 3, 7, 6, 5, 4, 2, 1 ],
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 3, 2, 7, 5, 4, 1, 6 ],
[ 9, 8, 4, 3, 7, 6, 5, 2, 1 ],
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
