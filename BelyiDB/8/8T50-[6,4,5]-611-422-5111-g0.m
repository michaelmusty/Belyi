s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,4,5]-611-422-5111-g0";
s`BelyiDBFilename := "8T50-[6,4,5]-611-422-5111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 8, 2, 3, 5, 1, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 5, 2, 3, 4, 6, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 2, 1, 4, 7, 6, 5, 8, 3 ],
[ 1, 8, 3, 6, 5, 2, 4, 7 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 4, 8, 7, 5, 6, 1, 3, 2 ],
[ 8, 7, 1, 4, 5, 6, 3, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 2, 3, 7, 5, 4, 8, 1, 6 ],
[ 1, 2, 5, 4, 8, 7, 3, 6 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 2, 3, 5, 1, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 5, 2, 3, 4, 6, 7, 8, 1 ]:
 Order := 40320 > |
[ 6, 1, 2, 3, 4, 5, 7, 8 ],
[ 2, 1, 4, 5, 8, 7, 6, 3 ],
[ 1, 8, 3, 4, 7, 2, 6, 5 ]
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
[ 4, 8, 2, 3, 5, 1, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 5, 2, 3, 4, 6, 7, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 2, 8, 3, 1, 5, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 6, 1, 3, 4, 5, 7, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 1, 2, 4, 3, 7, 5, 8 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 1, 2, 4, 5, 6, 8, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 1, 3, 5, 2, 7, 4, 8 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 1, 4, 2, 6, 5, 8, 7, 3 ]
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
