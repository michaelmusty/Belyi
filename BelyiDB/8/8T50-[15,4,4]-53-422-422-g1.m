s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,4,4]-53-422-422-g1";
s`BelyiDBFilename := "8T50-[15,4,4]-53-422-422-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 7, 1, 6, 3, 8, 5, 4 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 2, 8, 4, 3, 6, 5, 1, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 8, 1, 5, 6, 7, 4, 2 ],
[ 4, 3, 8, 1, 7, 2, 5, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 8, 3, 1, 7, 6, 5, 4, 2 ],
[ 6, 3, 8, 2, 7, 1, 5, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 5, 6, 8, 4, 2, 1 ],
[ 3, 8, 7, 1, 6, 5, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 7, 1, 6, 3, 8, 5, 4 ],
\[ 2, 3, 8, 5, 4, 7, 6, 1 ],
\[ 2, 8, 4, 3, 6, 5, 1, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 4, 7, 6, 5, 8, 3, 2, 1 ],
[ 4, 8, 7, 6, 1, 5, 3, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 7, 1, 6, 3, 8, 5, 4 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 2, 8, 4, 3, 6, 5, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 3, 8, 1, 7, 4, 6, 2 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 7, 1, 5, 4, 8, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 3, 1, 6, 2, 8, 5, 4 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 2, 4, 1, 3, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 6, 7, 2, 4, 1, 5 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 8, 6, 4, 5, 7, 2, 3, 1 ]
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
