s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[4,12,4]-422-431-44-g1";
s`BelyiDBFilename := "8T50-[4,12,4]-422-431-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 12, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 3, 6, 4, 7, 5, 1 ],
[ 5, 8, 1, 3, 4, 7, 2, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 3, 6, 4, 7, 5, 1 ],
[ 5, 8, 1, 3, 4, 7, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 5, 4, 2, 3, 7, 1, 8 ],
[ 3, 7, 4, 5, 1, 2, 8, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 3, 5, 2, 4, 1, 6, 8 ],
[ 5, 6, 4, 2, 7, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 8, 5, 4, 6, 1, 3, 7, 2 ],
[ 3, 5, 8, 6, 4, 2, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 2, 8, 3, 6, 4, 7, 5, 1 ],
\[ 5, 8, 1, 3, 4, 7, 2, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 6, 4, 3, 7, 5, 1 ],
[ 4, 8, 1, 5, 3, 7, 2, 6 ]
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
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 3, 6, 4, 7, 5, 1 ],
[ 5, 8, 1, 3, 4, 7, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 5, 4, 2, 3, 7, 1, 8 ],
[ 3, 7, 4, 5, 1, 2, 8, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 3, 5, 2, 4, 1, 6, 8 ],
[ 5, 6, 4, 2, 7, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 8, 5, 4, 6, 1, 3, 7, 2 ],
[ 3, 5, 8, 6, 4, 2, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 2, 8, 6, 4, 3, 7, 5, 1 ],
[ 4, 8, 1, 5, 3, 7, 2, 6 ]
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
