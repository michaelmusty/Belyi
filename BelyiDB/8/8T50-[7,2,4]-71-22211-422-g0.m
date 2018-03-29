s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[7,2,4]-71-22211-422-g0";
s`BelyiDBFilename := "8T50-[7,2,4]-71-22211-422-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 1, 7, 4, 6, 8, 5, 2 ],
[ 4, 2, 8, 1, 5, 7, 6, 3 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 1, 7, 4, 6, 8, 5, 2 ],
\[ 4, 2, 8, 1, 5, 7, 6, 3 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 1, 7, 4, 6, 8, 5, 2 ],
\[ 4, 2, 8, 1, 5, 7, 6, 3 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 1, 7, 4, 6, 8, 5, 2 ],
\[ 4, 2, 8, 1, 5, 7, 6, 3 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 5, 4, 3, 2, 1, 6, 8, 7 ],
[ 4, 3, 2, 1, 6, 8, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 7, 4, 6, 8, 5, 2 ],
\[ 4, 2, 8, 1, 5, 7, 6, 3 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 3, 2, 1, 6, 5, 4, 8, 7 ],
[ 2, 1, 6, 5, 4, 8, 3, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 1, 7, 4, 6, 8, 5, 2 ],
\[ 4, 2, 8, 1, 5, 7, 6, 3 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 7, 1, 2, 3, 4, 5, 6, 8 ],
[ 4, 8, 3, 1, 7, 6, 5, 2 ],
[ 8, 3, 1, 7, 6, 5, 4, 2 ]
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
[ 3, 1, 7, 4, 6, 8, 5, 2 ],
[ 4, 2, 8, 1, 5, 7, 6, 3 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 7, 5, 4, 6, 2, 8, 1 ],
[ 4, 8, 6, 1, 5, 3, 7, 2 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 6, 2, 5, 7, 4, 1, 8 ],
[ 8, 7, 3, 4, 6, 5, 2, 1 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ]
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
