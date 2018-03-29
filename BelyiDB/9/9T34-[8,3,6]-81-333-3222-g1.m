s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,3,6]-81-333-3222-g1";
s`BelyiDBFilename := "9T34-[8,3,6]-81-333-3222-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 6, 3, 9, 1, 7, 4, 8, 5, 2 ],
[ 7, 4, 9, 2, 6, 8, 1, 5, 3 ]
],
[ PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 3, 4, 5, 6, 1, 2, 8, 9, 7 ],
[ 7, 5, 6, 1, 2, 3, 4, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 6, 3, 5, 1, 2, 4, 8, 9, 7 ],
[ 7, 4, 5, 2, 6, 3, 1, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 4, 5, 7, 6, 8, 1, 9, 2, 3 ],
[ 5, 6, 8, 9, 1, 2, 4, 3, 7 ]
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
[ 7, 8, 6, 2, 5, 4, 3, 9, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 8, 6, 9, 5, 4, 2, 3, 1, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 5, 9, 3, 1, 4, 2, 8, 7 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 4, 9, 6, 5, 1, 3, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 7, 3, 9, 2, 8, 6, 1, 5 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 4, 2, 3, 8, 9, 1, 5, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 7, 8, 5, 3, 6, 4, 1, 2 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 8, 4, 9, 6, 5, 1, 2, 3 ]
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
