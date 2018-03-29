s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,12,2]-8-431-221111-g0";
s`BelyiDBFilename := "8T50-[8,12,2]-8-431-221111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 12, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 2, 1, 3, 4, 8, 6, 7 ],
[ 6, 3, 2, 4, 5, 1, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 2, 1, 3, 4, 8, 6, 7 ],
[ 6, 3, 2, 4, 5, 1, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 1, 7, 4, 5, 6, 3, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 2, 7, 4, 5, 6, 3 ],
[ 2, 1, 3, 8, 5, 6, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 5, 3, 4, 2, 6, 7 ],
[ 2, 1, 6, 4, 5, 3, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 1, 3, 4, 8, 6, 7 ],
\[ 6, 3, 2, 4, 5, 1, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 2, 1, 3, 7, 5, 6, 4 ],
[ 1, 3, 2, 4, 8, 6, 7, 5 ]
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
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 2, 1, 3, 4, 8, 6, 7 ],
[ 6, 3, 2, 4, 5, 1, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 6, 3, 4, 5, 2, 7 ],
[ 2, 1, 7, 4, 5, 6, 3, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 2, 7, 4, 5, 6, 3 ],
[ 2, 1, 3, 8, 5, 6, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 5, 3, 4, 2, 6, 7 ],
[ 2, 1, 6, 4, 5, 3, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 2, 1, 3, 7, 5, 6, 4 ],
[ 1, 3, 2, 4, 8, 6, 7, 5 ]
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
