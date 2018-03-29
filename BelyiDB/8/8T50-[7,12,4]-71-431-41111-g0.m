s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[7,12,4]-71-431-41111-g0";
s`BelyiDBFilename := "8T50-[7,12,4]-71-431-41111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 12, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 7, 3, 5, 6, 2, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 5, 2, 3, 4, 8, 6, 7 ],
[ 8, 1, 3, 4, 5, 2, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 3, 1, 2, 4, 8, 5, 6, 7 ],
[ 8, 2, 3, 1, 4, 6, 7, 5 ]
],
[ PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 8, 2, 7, 4, 5, 6, 3 ],
[ 4, 1, 3, 8, 5, 6, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 7, 3, 5, 6, 2, 8, 1 ],
\[ 1, 8, 6, 3, 4, 5, 2, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 4, 2, 3, 8, 5, 6, 7 ],
[ 8, 1, 3, 4, 2, 6, 7, 5 ]
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
[ 4, 7, 3, 5, 6, 2, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 5, 3, 6, 7, 2, 8 ],
[ 8, 2, 7, 1, 3, 5, 6, 4 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 4, 2, 5, 6, 1, 3, 8 ],
[ 8, 6, 3, 2, 4, 5, 1, 7 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 4, 2, 5, 1, 7, 3, 8 ],
[ 8, 5, 3, 2, 4, 1, 6, 7 ],
[ 2, 3, 8, 4, 5, 6, 7, 1 ]
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
