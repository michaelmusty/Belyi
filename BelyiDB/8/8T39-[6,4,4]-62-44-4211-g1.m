s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T39-[6,4,4]-62-44-4211-g1";
s`BelyiDBFilename := "8T39-[6,4,4]-62-44-4211-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 3, 6, 1, 4, 7, 2, 5 ],
[ 6, 3, 5, 2, 4, 1, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 8, 3, 6, 1, 4, 7, 2, 5 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 8, 3, 6, 1, 4, 7, 2, 5 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 8, 3, 6, 1, 4, 7, 2, 5 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 3, 6, 1, 4, 7, 2, 5 ],
[ 6, 3, 5, 2, 4, 1, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 8, 3, 6, 1, 4, 7, 2, 5 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 7, 3, 6, 1, 4, 8, 5, 2 ],
[ 1, 3, 5, 2, 4, 6, 8, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 3, 6, 1, 4, 7, 2, 5 ],
[ 6, 3, 5, 2, 4, 1, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 7, 5, 6, 1, 2, 8, 3, 4 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ],
[ 6, 3, 5, 2, 4, 1, 7, 8 ]
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
