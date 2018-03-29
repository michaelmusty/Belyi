s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,10,2]-8-521-221111-g0";
s`BelyiDBFilename := "8T50-[8,10,2]-8-521-221111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 10, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 7, 3, 4, 5, 6, 2 ],
[ 2, 1, 8, 4, 5, 6, 7, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 7, 3, 4, 5, 6, 2 ],
[ 2, 1, 8, 4, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 4, 5, 7, 6 ],
[ 3, 2, 1, 4, 5, 6, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 2, 3, 4, 7, 6, 5 ],
[ 2, 1, 3, 4, 5, 8, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 4, 6, 5, 7 ],
[ 3, 2, 1, 4, 5, 7, 6, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 1, 8, 4, 5, 6, 7, 3 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 5, 4, 6, 7 ],
[ 3, 2, 1, 4, 6, 5, 7, 8 ]
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
[ 1, 8, 7, 3, 4, 5, 6, 2 ],
[ 2, 1, 8, 4, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 4, 5, 7, 6 ],
[ 3, 2, 1, 4, 5, 6, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 2, 3, 4, 7, 6, 5 ],
[ 2, 1, 3, 4, 5, 8, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 4, 6, 5, 7 ],
[ 3, 2, 1, 4, 5, 7, 6, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 1, 8, 3, 5, 4, 6, 7 ],
[ 3, 2, 1, 4, 6, 5, 7, 8 ]
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
