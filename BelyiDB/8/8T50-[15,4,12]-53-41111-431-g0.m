s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,4,12]-53-41111-431-g0";
s`BelyiDBFilename := "8T50-[15,4,12]-53-41111-431-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 4, 12 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 2, 6, 4, 5, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 2, 4, 5, 6, 3, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 1, 2, 5, 3, 6, 4, 7, 8 ],
[ 3, 1, 2, 4, 6, 8, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 5, 2, 3, 1, 6, 4, 7, 8 ],
[ 1, 4, 2, 3, 6, 8, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 2, 6, 3, 4, 5, 8, 7, 1 ],
[ 5, 8, 1, 3, 4, 6, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 2, 6, 4, 5, 1, 7 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8 ],
\[ 7, 2, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 2, 6, 4, 5, 8, 7, 1 ],
[ 5, 8, 2, 1, 4, 6, 3, 7 ]
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
[ 3, 8, 2, 6, 4, 5, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 2, 4, 5, 6, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 1, 8, 6, 4, 5, 2, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 1, 7, 4, 5, 6, 3, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 8, 6, 3, 2, 4, 1, 7 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 7, 5, 3, 6, 4, 2, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 8, 2, 1, 4, 5, 6, 3 ],
[ 2, 3, 4, 1, 5, 6, 7, 8 ],
[ 3, 2, 8, 5, 6, 7, 4, 1 ]
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
