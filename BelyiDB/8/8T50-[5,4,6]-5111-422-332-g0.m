s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[5,4,6]-5111-422-332-g0";
s`BelyiDBFilename := "8T50-[5,4,6]-5111-422-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 5, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 2, 3, 1, 8, 4, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 1, 2, 5, 4, 7, 8, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 2, 3, 1, 8, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 3, 1, 2, 5, 4, 7, 8, 6 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 2, 3, 1, 8, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 3, 1, 2, 5, 4, 7, 8, 6 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 2, 3, 1, 8, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 3, 1, 2, 5, 4, 7, 8, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 8, 1, 5, 6, 7, 4, 2 ],
[ 4, 3, 8, 1, 7, 5, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 5, 2, 3, 1, 8, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 3, 1, 2, 5, 4, 7, 8, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 8, 1, 6, 7, 5, 4, 2 ],
[ 6, 3, 8, 1, 7, 4, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 5, 2, 3, 1, 8, 4, 7, 6 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 3, 1, 2, 5, 4, 7, 8, 6 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 8, 5, 6, 7, 3, 2, 4, 1 ],
[ 2, 8, 6, 5, 7, 3, 4, 1 ]
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
[ 5, 2, 3, 1, 8, 4, 7, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 1, 2, 5, 4, 7, 8, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 8, 3, 2, 5, 4, 7, 1 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 3, 2, 5, 6, 4, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 2, 8, 4, 5, 7, 1, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 8, 1, 4, 3, 6, 7, 5, 2 ]
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
