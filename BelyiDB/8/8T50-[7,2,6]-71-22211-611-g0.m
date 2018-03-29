s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[7,2,6]-71-22211-611-g0";
s`BelyiDBFilename := "8T50-[7,2,6]-71-22211-611-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 2, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 3, 1, 2, 4, 5, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 5, 3, 4, 6, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 3, 2, 5, 4, 6, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 8, 2, 4, 3, 6, 5, 7, 1 ],
[ 2, 4, 3, 6, 5, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 8, 2, 3, 5, 4, 7, 6, 1 ],
[ 2, 3, 5, 4, 7, 6, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 8, 3, 2, 4, 6, 5, 7, 1 ],
[ 3, 2, 4, 6, 5, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 7, 3, 1, 2, 4, 5, 6, 8 ],
\[ 8, 3, 2, 5, 4, 6, 7, 1 ],
\[ 2, 5, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 8, 2, 4, 3, 5, 7, 6, 1 ],
[ 2, 4, 3, 5, 7, 6, 8, 1 ]
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
[ 7, 3, 1, 2, 4, 5, 6, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 5, 3, 4, 6, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 3, 1, 6, 4, 2, 5, 8 ],
[ 8, 3, 2, 5, 4, 6, 7, 1 ],
[ 2, 6, 3, 4, 7, 5, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 8, 1, 3, 5, 4, 6, 7 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 4, 2, 3, 5, 6, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 7, 8, 3, 5, 4, 6, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 8, 2, 3, 5, 6, 7, 1, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 8, 1, 3, 5, 7, 4, 6 ],
[ 2, 1, 4, 3, 6, 5, 7, 8 ],
[ 4, 2, 3, 7, 6, 8, 5, 1 ]
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
