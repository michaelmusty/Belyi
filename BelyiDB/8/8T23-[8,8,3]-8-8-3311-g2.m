s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T23-[8,8,3]-8-8-3311-g2";
s`BelyiDBFilename := "8T23-[8,8,3]-8-8-3311-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 6, 7, 8, 1, 2, 3, 4, 5 ],
[ 3, 5, 4, 2, 7, 1, 8, 6 ],
[ 3, 2, 8, 5, 7, 6, 4, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 7, 8, 1, 2, 3, 4, 5 ],
\[ 3, 5, 4, 2, 7, 1, 8, 6 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 7, 8, 1, 2, 3, 4, 5 ],
\[ 3, 5, 4, 2, 7, 1, 8, 6 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 6, 7, 8, 1, 2, 3, 4, 5 ],
\[ 3, 5, 4, 2, 7, 1, 8, 6 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 6, 7, 8, 1, 2, 3, 4, 5 ],
[ 7, 4, 6, 5, 3, 8, 2, 1 ],
[ 2, 4, 3, 1, 6, 8, 7, 5 ]
],
[ PermutationGroup<8 |  
\[ 6, 7, 8, 1, 2, 3, 4, 5 ],
\[ 3, 5, 4, 2, 7, 1, 8, 6 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 3, 8, 2, 1, 7, 4, 6, 5 ],
[ 2, 4, 3, 1, 6, 8, 7, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 6, 7, 8, 1, 2, 3, 4, 5 ],
[ 3, 5, 4, 2, 7, 1, 8, 6 ],
[ 3, 2, 8, 5, 7, 6, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 48 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 7, 1, 8, 6, 3, 5, 4, 2 ],
[ 3, 2, 8, 5, 7, 6, 4, 1 ]
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
