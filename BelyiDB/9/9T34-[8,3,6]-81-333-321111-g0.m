s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,3,6]-81-333-321111-g0";
s`BelyiDBFilename := "9T34-[8,3,6]-81-333-321111-g0.m";
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
[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 9, 4, 2, 3, 7, 5, 6, 1, 8 ],
[ 9, 8, 3, 4, 2, 6, 7, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 5, 9, 2, 1, 4, 8, 6, 7, 3 ],
[ 6, 4, 3, 9, 5, 1, 7, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 6, 4, 2, 3, 1, 5, 9, 7, 8 ],
[ 9, 5, 3, 4, 2, 6, 1, 8, 7 ]
],
[ PermutationGroup<9 |  
\[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 3, 1, 2, 9, 7, 5, 6, 4, 8 ],
[ 9, 2, 3, 1, 8, 6, 7, 5, 4 ]
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
[ 7, 3, 5, 1, 4, 8, 6, 2, 9 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 3, 7, 1, 4, 5, 6, 9, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 9, 2, 7, 4, 6, 1, 5, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 9, 2, 3, 4, 7, 5, 6, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 7, 2, 1, 4, 5, 8, 6, 9 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 6, 2, 3, 4, 5, 7, 1, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 1, 5, 3, 7, 8, 2, 4, 9 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 1, 6, 3, 7, 5, 9, 4, 8, 2 ]
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
