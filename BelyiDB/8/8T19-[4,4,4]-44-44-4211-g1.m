s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T19-[4,4,4]-44-44-4211-g1";
s`BelyiDBFilename := "8T19-[4,4,4]-44-44-4211-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 6, 5, 4, 1, 8, 3, 2, 7 ],
[ 8, 1, 2, 6, 5, 4, 7, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 6, 5, 4, 1, 8, 3, 2, 7 ],
\[ 8, 1, 2, 6, 5, 4, 7, 3 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 6, 5, 4, 1, 8, 3, 2, 7 ],
\[ 8, 1, 2, 6, 5, 4, 7, 3 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 6, 5, 4, 1, 8, 3, 2, 7 ],
\[ 8, 1, 2, 6, 5, 4, 7, 3 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 4, 7, 6, 3, 2, 1, 8, 5 ],
[ 2, 3, 8, 4, 7, 6, 5, 1 ]
],
[ PermutationGroup<8 |  
\[ 6, 7, 4, 8, 3, 2, 1, 5 ],
\[ 6, 5, 4, 1, 8, 3, 2, 7 ],
\[ 8, 1, 2, 6, 5, 4, 7, 3 ]:
 Order := 32 > |
[ 4, 7, 6, 3, 2, 1, 8, 5 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 1, 8, 3, 7, 4, 5, 6, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 > |
[ 6, 7, 4, 8, 3, 2, 1, 5 ],
[ 6, 5, 4, 1, 8, 3, 2, 7 ],
[ 8, 1, 2, 6, 5, 4, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 32 > |
[ 7, 6, 5, 3, 8, 1, 2, 4 ],
[ 2, 3, 8, 6, 5, 4, 7, 1 ],
[ 4, 7, 6, 3, 2, 1, 8, 5 ]
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
