s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T41-[6,4,4]-62-4211-44-g1";
s`BelyiDBFilename := "8T41-[6,4,4]-62-4211-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 2, 8, 1, 4, 5, 7, 6, 3 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 2, 8, 1, 4, 5, 7, 6, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 2, 8, 1, 4, 5, 7, 6, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 2, 8, 1, 4, 5, 7, 6, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 2, 8, 1, 4, 5, 7, 6, 3 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 2, 8, 1, 4, 5, 7, 6, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 1, 8, 4, 5, 7, 6, 2 ],
[ 6, 7, 4, 1, 2, 3, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 2, 8, 1, 4, 5, 7, 6, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 3, 1, 7, 5, 6, 4, 2 ],
[ 4, 6, 7, 2, 3, 1, 8, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 2, 8, 1, 4, 5, 7, 6, 3 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 5, 4, 6, 2, 8, 1, 3, 7 ],
[ 8, 3, 1, 7, 5, 6, 4, 2 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 3, 1, 4, 6, 5, 7, 2 ],
[ 7, 5, 4, 2, 3, 1, 8, 6 ]
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
