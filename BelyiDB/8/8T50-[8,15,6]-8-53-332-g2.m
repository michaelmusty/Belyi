s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,15,6]-8-53-332-g2";
s`BelyiDBFilename := "8T50-[8,15,6]-8-53-332-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 15, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 16;
s`BelyiDBPointedSize := 16;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 1, 5, 6, 3, 8, 2 ],
[ 7, 3, 8, 6, 1, 4, 5, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 1, 5, 6, 3, 8, 2 ],
[ 7, 3, 8, 6, 1, 4, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 3, 4, 5, 6, 1, 7, 8, 2 ],
[ 7, 5, 8, 1, 2, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 6, 1, 7, 3, 8, 2, 4 ],
[ 6, 3, 7, 5, 8, 1, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 8, 1, 5, 7, 3, 4, 6 ],
[ 2, 3, 1, 6, 7, 4, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 8, 6, 2, 1, 3, 5 ],
[ 3, 6, 5, 7, 1, 8, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 8, 1, 6, 3, 7, 4, 5 ],
[ 2, 3, 1, 5, 7, 8, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 4, 5, 8, 7, 2, 3, 1 ],
[ 4, 8, 6, 7, 2, 3, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 7, 5, 1, 2, 4, 8, 3 ],
[ 7, 4, 5, 8, 6, 3, 1, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 5, 2, 6, 3, 8, 1 ],
[ 7, 8, 4, 6, 1, 3, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 3, 7, 6, 2, 8, 1, 4 ],
[ 6, 7, 5, 2, 8, 1, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 8, 7, 2, 6, 1, 4, 3 ],
[ 2, 6, 4, 8, 7, 1, 5, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 6, 1, 5, 8, 7, 2, 3 ],
[ 5, 3, 7, 8, 1, 4, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 3, 7, 5, 8, 2, 4, 1, 6 ],
[ 4, 7, 5, 1, 6, 3, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 5, 6, 7, 3, 1, 8, 4 ],
[ 7, 6, 1, 5, 8, 2, 3, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 8, 5, 2, 3, 1, 6 ],
[ 3, 7, 5, 6, 1, 4, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 7, 1, 5, 6, 3, 8, 2 ],
\[ 7, 3, 8, 6, 1, 4, 5, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 5, 1, 7, 3, 2, 8, 4 ],
[ 7, 3, 6, 5, 8, 2, 1, 4 ]
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
[ 4, 7, 1, 5, 6, 3, 8, 2 ],
[ 7, 3, 8, 6, 1, 4, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 3, 4, 5, 6, 1, 7, 8, 2 ],
[ 7, 5, 8, 1, 2, 3, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 6, 1, 7, 3, 8, 2, 4 ],
[ 6, 3, 7, 5, 8, 1, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 8, 1, 5, 7, 3, 4, 6 ],
[ 2, 3, 1, 6, 7, 4, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 8, 6, 2, 1, 3, 5 ],
[ 3, 6, 5, 7, 1, 8, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 8, 1, 6, 3, 7, 4, 5 ],
[ 2, 3, 1, 5, 7, 8, 4, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 4, 5, 8, 7, 2, 3, 1 ],
[ 4, 8, 6, 7, 2, 3, 1, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 7, 5, 1, 2, 4, 8, 3 ],
[ 7, 4, 5, 8, 6, 3, 1, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 5, 2, 6, 3, 8, 1 ],
[ 7, 8, 4, 6, 1, 3, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 3, 7, 6, 2, 8, 1, 4 ],
[ 6, 7, 5, 2, 8, 1, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 5, 8, 7, 2, 6, 1, 4, 3 ],
[ 2, 6, 4, 8, 7, 1, 5, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 6, 1, 5, 8, 7, 2, 3 ],
[ 5, 3, 7, 8, 1, 4, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 3, 7, 5, 8, 2, 4, 1, 6 ],
[ 4, 7, 5, 1, 6, 3, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 5, 6, 7, 3, 1, 8, 4 ],
[ 7, 6, 1, 5, 8, 2, 3, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 7, 8, 5, 2, 3, 1, 6 ],
[ 3, 7, 5, 6, 1, 4, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 5, 1, 7, 3, 2, 8, 4 ],
[ 7, 3, 6, 5, 8, 2, 1, 4 ]
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
