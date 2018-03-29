s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[5,6,10]-5111-332-521-g0";
s`BelyiDBFilename := "8T50-[5,6,10]-5111-332-521-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 5, 6, 10 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 2, 8, 4, 3, 6, 7, 5, 1 ],
[ 7, 8, 1, 4, 3, 5, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 6, 7, 8 ],
[ 8, 1, 4, 3, 6, 7, 5, 2 ],
[ 8, 4, 3, 7, 2, 5, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 6, 7, 8 ],
[ 8, 6, 1, 5, 4, 7, 2, 3 ],
[ 7, 8, 5, 4, 3, 2, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 6, 7, 8 ],
[ 2, 8, 6, 7, 4, 3, 5, 1 ],
[ 1, 6, 5, 7, 8, 3, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 6, 7, 8 ],
[ 5, 8, 4, 7, 6, 1, 3, 2 ],
[ 8, 7, 3, 1, 6, 5, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 2, 8, 4, 3, 6, 7, 5, 1 ],
\[ 7, 8, 1, 4, 3, 5, 6, 2 ]:
 Order := 40320 > |
[ 5, 1, 2, 3, 4, 6, 7, 8 ],
[ 2, 1, 6, 3, 7, 4, 8, 5 ],
[ 1, 4, 6, 8, 2, 3, 5, 7 ]
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
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 2, 8, 4, 3, 6, 7, 5, 1 ],
[ 7, 8, 1, 4, 3, 5, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 7, 3, 2, 5, 6, 4, 8, 1 ],
[ 4, 8, 3, 2, 6, 5, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 6, 8, 5, 4, 7, 2, 1 ],
[ 4, 8, 7, 1, 5, 2, 6, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 5, 8, 4, 6, 7, 3, 1, 2 ],
[ 1, 7, 8, 6, 3, 4, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 6, 2, 5, 7, 3, 4, 1 ],
[ 4, 8, 3, 6, 7, 2, 5, 1 ]
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
