s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,2,12]-53-22211-431-g0";
s`BelyiDBFilename := "8T50-[15,2,12]-53-22211-431-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 2, 12 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 5, 1, 3, 4, 8, 6, 7 ],
[ 8, 3, 2, 4, 5, 7, 6, 1 ],
[ 2, 8, 4, 5, 3, 6, 1, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 8, 5, 3, 4, 2, 7, 6, 1 ],
[ 5, 3, 4, 2, 8, 6, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 6, 7, 4, 3, 5, 1, 2, 8 ],
[ 7, 4, 3, 5, 6, 2, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 6, 7, 3, 5, 4, 1, 2, 8 ],
[ 7, 3, 5, 4, 6, 2, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 5, 8, 3, 7, 1, 6, 4, 2 ],
[ 8, 3, 7, 1, 5, 4, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 5, 1, 3, 4, 8, 6, 7 ],
\[ 8, 3, 2, 4, 5, 7, 6, 1 ],
\[ 2, 8, 4, 5, 3, 6, 1, 7 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 1, 7, 4, 3, 6, 5, 2, 8 ],
[ 7, 4, 3, 6, 1, 2, 8, 5 ]
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
[ 2, 5, 1, 3, 4, 8, 6, 7 ],
[ 8, 3, 2, 4, 5, 7, 6, 1 ],
[ 2, 8, 4, 5, 3, 6, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 1, 7, 2, 4, 3, 6, 5 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 1, 3, 5, 6, 8, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 5, 7, 8, 4, 3, 6, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 8, 2, 5, 6, 1, 7, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 1, 5, 2, 8, 7, 4, 3 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 1, 3, 8, 7, 4, 2, 5, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 7, 2, 8, 6, 4, 3, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 8, 4, 7, 5, 2, 6, 1, 3 ]
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
