s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,5,10]-611-5111-521-g0";
s`BelyiDBFilename := "8T50-[6,5,10]-611-5111-521-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 5, 10 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 2, 1, 3, 4, 5, 6, 8 ],
[ 2, 3, 4, 8, 5, 6, 7, 1 ],
[ 2, 1, 3, 5, 6, 7, 8, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 1, 6, 3, 4, 7, 5, 8, 2 ],
[ 2, 1, 8, 3, 4, 6, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 2, 3, 7, 5, 4, 8, 1 ],
[ 1, 8, 2, 3, 6, 5, 4, 7 ]
],
[ PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 7, 1, 3, 4, 5, 8, 6, 2 ],
[ 7, 2, 8, 3, 4, 5, 1, 6 ]
],
[ PermutationGroup<8 |  
\[ 7, 2, 1, 3, 4, 5, 6, 8 ],
\[ 2, 3, 4, 8, 5, 6, 7, 1 ],
\[ 2, 1, 3, 5, 6, 7, 8, 4 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 7, 1, 8, 4, 5, 6, 3, 2 ],
[ 6, 2, 8, 7, 4, 5, 1, 3 ]
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
[ 7, 2, 1, 3, 4, 5, 6, 8 ],
[ 2, 3, 4, 8, 5, 6, 7, 1 ],
[ 2, 1, 3, 5, 6, 7, 8, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 7, 2, 4, 3, 5, 1, 8 ],
[ 2, 3, 4, 8, 5, 6, 7, 1 ],
[ 7, 2, 5, 3, 6, 8, 1, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 7, 3, 5, 8, 6, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 1, 3, 5, 4, 7, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 1, 7, 4, 3, 5, 2, 8 ],
[ 2, 3, 4, 8, 5, 6, 7, 1 ],
[ 1, 7, 5, 3, 6, 8, 2, 4 ]
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
