s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,2,12]-62-22211-431-g0";
s`BelyiDBFilename := "8T50-[6,2,12]-62-22211-431-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 2, 12 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 6, 4, 2, 7, 1, 5, 3 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 5, 3, 8, 4, 7, 1, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 6, 8, 3, 4, 7, 1, 5, 2 ],
[ 8, 3, 4, 7, 1, 6, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 1, 8, 3, 5, 4, 7, 6, 2 ],
[ 8, 3, 5, 4, 7, 1, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 3, 8, 1, 5, 4, 6, 7, 2 ],
[ 8, 1, 5, 4, 6, 3, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 3, 8, 1, 4, 6, 5, 7, 2 ],
[ 8, 1, 4, 6, 5, 3, 2, 7 ]
],
[ PermutationGroup<8 |  
\[ 8, 6, 4, 2, 7, 1, 5, 3 ],
\[ 2, 1, 4, 3, 6, 5, 7, 8 ],
\[ 5, 3, 8, 4, 7, 1, 6, 2 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 7, 2, 8, 5, 4, 6, 1, 3 ],
[ 2, 8, 5, 4, 6, 7, 3, 1 ]
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
[ 8, 6, 4, 2, 7, 1, 5, 3 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 5, 3, 8, 4, 7, 1, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 8, 5, 7, 1, 3, 4, 6 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 6, 2, 5, 7, 4, 8, 3, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 8, 1, 7, 5, 4, 2, 6, 3 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 1, 5, 8, 6, 3, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 3, 2, 8, 6, 4, 1, 7 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 7, 4, 1, 5, 2, 6, 8, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 1, 6, 8, 7, 3, 4, 2 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 1, 8, 5, 7, 2, 4, 6, 3 ]
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
