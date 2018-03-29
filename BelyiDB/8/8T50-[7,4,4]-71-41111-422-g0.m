s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[7,4,4]-71-41111-422-g0";
s`BelyiDBFilename := "8T50-[7,4,4]-71-41111-422-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 3, 5, 6, 7, 8, 2 ],
[ 1, 2, 8, 3, 5, 4, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 1, 3, 5, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 5, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 1, 3, 5, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 5, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 4, 1, 3, 5, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 5, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 2, 3, 7, 5, 4, 8, 6 ],
[ 4, 1, 2, 3, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 4, 1, 3, 5, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 5, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 7, 3, 4, 8, 6, 5, 2 ],
[ 2, 1, 8, 3, 4, 7, 6, 5 ]
],
[ PermutationGroup<8 |  
\[ 4, 1, 3, 5, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 5, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 1, 7, 3, 4, 5, 2, 8, 6 ],
[ 2, 1, 6, 3, 4, 5, 8, 7 ]
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
[ 4, 1, 3, 5, 6, 7, 8, 2 ],
[ 1, 2, 8, 3, 5, 4, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 2, 5, 6, 7, 3, 8 ],
[ 1, 2, 3, 7, 5, 4, 8, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 2, 5, 7, 6, 8, 3 ],
[ 1, 2, 3, 8, 6, 4, 7, 5 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ]
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
